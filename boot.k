;; -*- mode: Lisp-*-
(define! ((vau0 e _ e)) ((vau0 _ x (car x)) define)
  (vau0 e args (define! e (car args) (eval e (car (cdr args))))))
(define vau vau0)
(define the-environment (vau0 e _ e))
(define wrap (record <wrap> (vau _ args (record <wrap> (car args)))))
(define unwrap (wrap (vau _ args (record-field (car args) 0))))
(define lambda
    (vau env args
         (wrap (eval env (cons vau (cons _ args))))))
(define list (lambda x x))
(define quote (vau _ x (car x)))
(define caar (lambda args (car (car (car args)))))
(define cadr (lambda args (car (cdr (car args)))))
(define cddr (lambda args (cdr (cdr (car args)))))
(define cdar (lambda args (cdr (car (car args)))))
(define caddr (lambda args (car (cddr (car args)))))
(define cadar (lambda args (car (cdar (car args)))))
(define cdddr (lambda args (cdr (cddr (car args)))))
(define cddar (lambda args (cdr (cdar (car args)))))
(define apply (wrap (vau env args (combine env (unwrap (car args)) (cadr args)))))
(define tag? (lambda x (eq? (tag (car x)) (cadr x))))
(define cons? (lambda x (eq? (tag (car x)) 'cons)))
(define symbol? (lambda x (eq? (tag (car x)) 'symbol)))
(define null? (lambda x (eq? (tag (car x)) 'null)))

(define list* (lambda x (if (cons? (cdr x)) (cons (car x) (apply list* (cdr x))) (car x))))

(define signal panic)

(define match-arglist
    (lambda args
      (if (cons? (car args))
          (if (eq? (car (car args)) _)
              (match-arglist (cdr (car args)) (cdr (cadr args)))
              (cons (list (car (car args)) (car (cadr args)))
                    (match-arglist (cdr (car args)) (cdr (cadr args)))))
          (if (symbol? (car args))
              (list args)
              (if (eq? (car args) _)
                  nil
                  (if (eq? (car args) (cadr args)) nil
                      (signal '(arglist-mismatch))))))))

;; Arglist pattern matching
(define vau1
    (vau0 env0 args0
          (if (eq? (car args0) _)
              (vau0 _ args
                    (eval (vecenv env0 (match-arglist (cadr args0) args))
                          (caddr args0)))
              (vau0 env args
                    (eval (vecenv env0 (match-arglist (cons (car args0) (cadr args0)) (cons env args)))
                          (caddr args0))))))
(define vau vau1)

(define cata
    (lambda (fmap algebra data)
      (algebra (fmap (lambda (child) (cata fmap algebra child)) data))))

(define foldr
    (lambda (kons knil ys)
      (if ys (kons (car ys) (foldr kons knil (cdr ys))) knil)))

(define foldl
    (lambda (op init ys)
      (if ys (foldl op (op init (car ys)) (cdr ys)) init)))

(define nth
    (lambda (a-list n)
      (if (= n 0)
          (car a-list)
          (nth (cdr a-list) (- n 1)))))

(define reverse
    (lambda (a-list)
      (foldl (lambda (result el) (cons el result)) nil a-list)))

(define append
    (lambda (a-list b-list)
      (foldr cons b-list a-list)))

(define map
    (lambda (f a-list)
      (reverse
       (foldl (lambda (rest el) (cons (f el) rest))
              nil a-list) )))

(define filter
    (lambda (f a-list)
      (reverse
       (foldl (lambda (rest el)
                (if (f el) (cons el rest) rest))
              nil a-list) )))

(define for!
    (lambda (f a-list)
      (foldl (lambda (_ el) (f el) nil)
             nil a-list)))

(define begin2
    (vau1 env (first second)
          ((wrap (vau0 _ _ (eval env second)))
           (eval env first))))

(define begin
    (vau0 env body
          (if body
              (if (cdr body)
                  (begin2
                   (eval env (car body))
                   (combine env begin (cdr body)))
                  (eval env (car body)))
              nil)))

;; Multiple forms as body
(define vau2
    (vau1 env (fenv fargs . body)
          (combine env vau1 (list fenv fargs (cons begin body)))))

(define vau vau2)

(define cond
    (vau env clauses
         (define aux
             (lambda (clause . rest)
               (if (eval env (car clause))
                   (combine env begin (cdr clause))
                   (combine env cond rest))))
         (if clauses
             (apply aux clauses)
             nil)))

(define when
    (vau env (test . args)
         (if (eval env test)
             (combine env begin args)
             nil)))

(define unless
    (vau env (test . args)
         (combine env when (cons (list not test) args))))

(define not (lambda (x) (if x nil t)))

(define case-vau
    (vau lexenv clauses
         (vau dynenv args
              (define aux
                  (lambda (clauses)
                    (if clauses
                        (begin
                         (define match
                             (call-with-condition-handler
                              (lambda (c) 'fail)
                              (lambda ()
                                (match-arglist (cons (caar clauses) (cadar clauses))
                                               (cons dynenv args)))))
                         (if (eq? match 'fail)
                             (aux (cdr clauses))
                             (combine (vecenv lexenv match)
                                      begin (cddar clauses))))
                        (signal '(arglist-mismatch)))))
              (aux clauses))))

(define and
    (vau0 env args
          (if (cons? args)
              (begin
               (define head (eval env (car args)))
               (when head
                 (if (cons? (cdr args))
                     (combine env and (cdr args))
                     head)))
              t)))
(define or
    (vau0 env args
          (if (cons? args)
              (begin
               (define head (eval env (car args)))
               (if head head (combine env or (cdr args))))
              nil)))

(define any?
    (lambda (pred ys)
      (foldr (vau env (head rest)
                  (or (pred (eval env head)) (eval env rest)))
                  nil ys)))
(define every?
    (lambda (pred ys)
      (foldr (vau env (head rest)
                  (and (pred (eval env head)) (eval env rest)))
             t ys)))

(define fib
    (lambda (x)
      (if (> x 1)
          (+ (fib (- x 1)) (fib (- x 2)))
          1)))

#+nil (define fib
    (wrap (cvau env args
                (lit 2 1)
                (ins 3 car 1)
                (ins 4 > 3 2)
                (branch 5 4
                        (begin
                         (lit 5 fib)
                         (ins 6 lookup 0 5)
                         (ins 7 unwrap 6)
                         (ins 8 - 3 2)
                         (lit 9 nil)
                         (ins 10 cons 8 9)
                         (ins 11 combine 0 7 10)
                         (lit 12 2)
                         (ins 13 - 3 12)
                         (ins 14 cons 13 9)
                         (ins 15 combine 0 7 14)
                         (ins 16 + 11 15)
                         (reg 16))
                        (begin
                         (reg 2)))
                (reg 5))))

;;; Setters

(define set!
    (vau env (place value)
         (mutate! env place (eval env value))))

(define push!
    (vau env (place value)
         (mutate!
          env place
          (cons (eval env value) (lookup env place)))))

(define inc!
    (vau env (place value)
         (mutate!
          env place
          (+ (eval env value) (lookup env place)))))

;;; Continuations

(define record?
    (lambda (object a-record-descriptor)
      (and (eq? (tag object) 'record)
           (eq? (record-descriptor object) a-record-descriptor))))

(define lookup-maybe
    (vau dynenv (env x default-expr)
         (define slot (list (lookup-slot (eval dynenv env) (eval dynenv x) '%unbound)))
         (if (eq? (car slot) '%unbound)
             (eval dynenv default-expr)
             (if (lookup-hook? (car slot))
                 (combine dynenv (lookup-hook-operative (car slot)) (list x))
                 (car slot)))))

(define lookup-slot
    (lambda (env x default)
      (if env
          (begin
           (define slot (list (lookup-local env x default)))
           (if (eq? (car slot) default)
               (lookup-slot (parent env) x default)
               (car slot)))
          default)))

(define primitive-call/cc call/cc)
(define primitive-invoke-continuation! invoke-continuation!)
(define *fluid-env* (vecenv nil nil))
(define call/cc
    (lambda (thunk)
      (primitive-call/cc
       (lambda (k)
         (define! k 'fluid-env *fluid-env*)
         (thunk k)))))
(define invoke-continuation!
    (lambda (cont value)
      (set! *fluid-env* (lookup cont 'fluid-env))
      (primitive-invoke-continuation! cont value)))

(define <fluid>
    (vau env (x)
         (define self (lookup-hook-operative (lookup-local env x nil)))
         (lookup-maybe *fluid-env* self (lookup self 'default-value))))

(define! <fluid> 'setter
  (vau env (x new-value)
       (define self (lookup-hook-operative (lookup-local env x nil)))
       (mutate! *fluid-env* self new-value)))

(define define-fluid
    (vau env (var . default-value-expr)
         (define! env var
           (record <lookup-hook>
                   (if default-value-expr
                       (vecenv <fluid> (list (list 'default-value (eval env (car default-value-expr)))))
                       (vecenv <fluid> (list (list 'name var))))))))

(define call-with-fluids
    (lambda (bindings thunk)
      (define saved-state *fluid-env*)
      (set! *fluid-env* (vecenv *fluid-env* bindings))
      (define result (thunk))
      (set! *fluid-env* saved-state)
      result))

(define with-fluids
    (vau env (bindings . body)
         (call-with-fluids
          (map (lambda (binding)
                 (list (lookup-hook-operative (lookup-slot env (car binding) nil))
                       (eval env (cadr binding))))
               bindings)
          (lambda () (eval env (cons begin body))))))

(define let/cc
    (vau env (var . body)
         (call/cc (eval env (list* lambda (list var) body)))))

(define catch
    (vau env (var . body)
         (call/cc
          (lambda (k)
            (call-with-fluids
             (list (list (lookup-hook-operative (lookup-slot env var nil)) k))
             (lambda () (combine env begin body)))))))

(define-fluid error-continuation
   (let/cc return
           (panic (let/cc k
                          (invoke-continuation! return k)))))
(define signal
    (lambda (condition)
      (let/cc k (invoke-continuation! error-continuation (cons k condition)))))

(define call-with-condition-handler
    (lambda (handler thunk)
      (let/cc normal-k
              (handler
               (let/cc abnormal-k
                       (with-fluids ((error-continuation abnormal-k))
                         (invoke-continuation! normal-k (thunk))))))))
(define ignore-errors
    (vau env body
         (call-with-condition-handler
          (lambda (c))
          (lambda () (combine env begin body)))))

;;; Partial evaluator

(define <code> (vecenv nil (list (list 'length 1))))
(define code?
    (lambda (object)
      (and (record? object <code>)
           (eq? (tag (code-reg object)) 'fixnum))))
(define code-reg
    (lambda (object)
      (record-field object 0)))

(define dynamic-tail?
    (lambda (list-a)
      (if (cons? list-a)
          (dynamic-tail? (cdr list-a))
          (code? list-a))))

(define list-dynamic?
    (lambda (list-a)
      (if (cons? list-a)
          (or (code? (car list-a))
              (list-dynamic? (cdr list-a)))
          (code? list-a))))

(define list-n-dynamic?
    (lambda (list-a n)
      (if (cons? list-a)
          (if (= n 0)
              (code? (car list-a))
              (list-n-dynamic? (cdr list-a) (- n 1)))
          (code? list-a))))

(define-fluid code-list)
(define-fluid next-reg)
;; `hashenv' of all paartial static environments
(define-fluid psenv-table (vecenv nil nil))
(define-fluid value-memo)
(define-fluid reg-info-value)
(define-fluid reg-info-effect)
(define-fluid dead-branch-continuation)

(define! <primitive> 'residualize
  (vau env (op . args)
       (define result
           (if (dynamic-tail? args)
               (emit-ins! 'combine nil op args)
               (apply emit-ins! (cons (lookup op 'name) args))))
       (define! reg-info-effect (code-reg result) (lookup op 'effect))
       result))
(define! <closure> 'residualize
  (vau env (op . args)
       (define result (emit-ins! 'combine
                                 (if (eq? (lookup op 'env-formal) _) nil env)
                                 op args))
       (define effect (lookup op 'effect))
       (define! reg-info-effect (code-reg result) effect)
       (when effect
         (psenv-invalidate! args)
         (unless (eq? (lookup op 'env-formal) _)
           (psenv-invalidate! env)))
       result))

(define! <primitive> 'expand
  (vau env (op . args) (combine env op args)))
(define! <closure> 'expand
  (vau env (op . args)
       (peval
        (pcombine
         nil
         (unwrap vecenv)
         (list
          (lookup op 'env)
          (list
           (list (lookup op 'env-formal) env)
           (list (lookup op 'args-formal) args))))
        (lookup op 'expr))))

(define residualize-when
    (lambda (f)
      (vau env (op . args)
           (combine env
                    (if (f args)
                        (lookup op 'residualize)
                        (lookup op 'expand))
                    (cons op args)))))

(define! <primitive> 'compile (residualize-when (lambda _ t)))
(define! <closure> 'compile (residualize-when list-dynamic?))

(for! (lambda (applicative)
        (define! (unwrap applicative) 'compile (residualize-when code?)))
      (list cons record wrap unwrap
            list list* cadr cddr caddr apply tag? cons? symbol? null? not
            code? code-reg))

(define! (unwrap match-arglist) 'compile
  (residualize-when (lambda (args) (list-n-dynamic? args 0))))

(for! (lambda (primitive-app)
        (define! (unwrap primitive-app) 'compile (residualize-when list-dynamic?)))
      (list car cdr record-descriptor record-field tag eq?))

(define! if 'compile
  (vau env (_ test then else)
       (define test (peval env test))
       (cond ((code? test)
              (define reg next-reg)
              (define then-value '%dead-branch)
              (define else-value '%dead-branch)
              (define reg-info-effect reg t) ;; TODO: less naive effect analysis
              (inc! next-reg 1)
              (push! code-list
                     (list 'branch reg (reify test)
                           ;; TODO: handle partial static environment store merge correctly
                           (with-fluids
                            ((code-list nil)
                             (value-memo (hashenv value-memo nil)))
                            (cons 'begin
                                  (collect-code-list
                                   (catch dead-branch-continuation
                                     (reify (set! then-value (peval env then)))))))
                           (with-fluids
                            ((code-list nil)
                             (value-memo (hashenv value-memo nil)))
                             (cons 'begin
                                  (collect-code-list
                                   (catch dead-branch-continuation
                                     (reify (set! else-value (peval env else)))))))))
              (if (code? then-value)
                  (record <code> reg)
                  (if (code? else-value)
                      (record <code> reg)
                      (if (eq? then-value '%dead-branch)
                          (if (eq? else-value '%dead-branch)
                              (invoke-continuation! dead-branch-continuation reg)
                              else-value)
                          (if (eq? else-value '%dead-branch)
                              then-value
                              (if (eq? then-value else-value)
                                  then-value
                                  (record <code> reg)))))))
             (test (peval env then))
             (t (peval env else)))))

(define! (unwrap primitive-call/cc) 'residualize
  (vau _ (_ thunk)
       (psenv-invalidate! thunk)
       (emit-ins! 'call/cc thunk)))

(define! (unwrap primitive-invoke-continuation!) 'residualize
  (vau _ (_ cont value)
       (invoke-continuation! dead-branch-continuation
                             (reify (emit-ins! 'invoke-continuation! cont value)))))

(define! (unwrap signal) 'residualize
  (vau _ (op . args)
       (invoke-continuation! dead-branch-continuation
                             (reify (emit-ins! 'combine nil op args)))))
(define! (unwrap signal) 'compile (residualize-when (lambda _ t)))

(define! begin2 'compile
  (vau env (_ first second)
       (peval env first)
       (peval env second)))
(define! (unwrap eval) 'compile (vau _ (_ env form) (peval env form)))
(define! (unwrap combine) 'compile  (vau _ (_ env op args) (pcombine env op args)))

(define! (unwrap vecenv) 'compile (residualize-when list-dynamic?))
(define! (unwrap vecenv) 'expand
  (vau _ (_ parent alist)
       (define result (vecenv parent alist))
       (define reg (code-reg (emit-ins! 'vecenv parent alist)))
       (define! psenv-table result t)
       (define! value-memo result reg)
       result))

(define! (unwrap define!) 'compile
  (vau _ (_ env key value)
       (define reg (code-reg (emit-ins! 'define! env key value)))
       (unless (bound? psenv-table env)
         (define! reg-info-effect reg t))
       (when (eq? (tag env) 'object)
         (if (bound? psenv-table env)
             (define! env key value)
             (unless (member? (lookup-maybe env '%volatile-slots nil) key)
               (signal (list 'non-volatile-slot-write env key)))))
       value))

(define! (unwrap mutate!) 'compile
  (vau _ (_ env key value)
       ;; TODO: This is probably too aggressive and wrong.
       ;; Make it conservative and correct.
       (define reg (code-reg (emit-ins! 'mutate! env key value)))
       (define! reg-info-effect reg t)
       (define process!
           (lambda (env)
             (when (bound? psenv-table env)
               (if (bound? env key)
                   (define! env key value)
                   (process! (parent env))))))
       (process! env)))

;; The following do not compile nested `vau', i.e. closures are
;; interpreted for now.  `reify' will compile `vau's when it sees one,
;; so we don't bother compiling `vau's that are only used during
;; expansion.
(define! vau0 'expand
  (vau env (_ . args)
       (define result (combine env vau0 args))
       (define reg (code-reg (emit-ins! 'vau env args)))
       (define! psenv-table result t)
       (define! value-memo result reg)
       (define! reg-info-value reg result)
       result))
(define! vau0 'compile (residualize-when list-dynamic?))

(define compile-print (lambda (x) x))
(define! (unwrap compile-print) 'compile
  (vau env (_ x) (print x) x))

(define record-fields
    (lambda (r)
      (define loop
          (lambda (i)
            (if (< i (lookup (record-descriptor r) 'length))
                (cons (record-field r i) (loop (+ i 1)))
                nil)))
      (loop 0)))

(define nub
    (lambda (a-list)
      (define mark-table (hashenv nil nil))
      (reverse
       (foldl (lambda (rest el)
                (if (bound? mark-table el)
                    rest
                    (begin
                     (define! mark-table el t)
                     (cons el rest))))
              nil a-list))))

(define remove
    (lambda (a-list el)
      (filter (lambda (a-el) (not (eq? a-el el))) a-list)))

(define member?
    (lambda (a-list el)
      (any? (lambda (a-el) (eq? a-el el)) a-list)))

(define all-keys
    (lambda (env)
      (when env
        (append (keys env)
                (all-keys (parent env))))))

(define reify
    (lambda (value)
      (lookup-maybe
       value-memo value
       (define! value-memo value
         (cond
           ((cons? value)
            (define reg (code-reg (emit-ins! 'cons (car value) (cdr value))))
            reg)
           ((code? value)
            (code-reg value))
           ((eq? (tag value) 'record)
            (define reg (code-reg (apply emit-ins! (list* 'record (record-descriptor value) (record-fields value)))))
            reg)
           (t
            (when (bound? psenv-table value)
              (signal (list 'broken-invariant value)))
            (define reg next-reg)
            (inc! next-reg 1)
            (push! code-list (list 'lit reg value))
            reg))))))

(define emit-ins!
    (lambda (ins . args)
      (define args (map reify args))
      (define reg next-reg)
      (inc! next-reg 1)
      (push! code-list (list* ins reg args))
      (record <code> reg)))

(define bound?
    (lambda (env key)
      (not (eq? (lookup-slot env key '%unbound) '%unbound))))

(define plookup
    (lambda (env key)
      (if env
          (if (code? env)
              (emit-ins! 'lookup env key)
              (begin
               (define slot (list (lookup-local env key '%unbound)))
               (cond ((or (eq? (car slot) '%unknown)
                          (member? (lookup-local env '%volatile-slots nil) key))
                      (emit-ins! 'lookup env key))
                     ((eq? (car slot) '%unbound) (plookup (parent env) key))
                     ((lookup-hook? (car slot))
                      (pcombine env (lookup-hook-operative (car slot)) (list key)))
                     (t (car slot)))))
          (emit-ins! 'vm-error (list 'unbound-key env key)))))

(define peval
    (lambda (env form)
      (cond ((cons? form)
             (pcombine env (peval env (car form)) (cdr form)))
            ((symbol? form) (plookup env form))
            (t form))))

(define pcombine
    (lambda (env op args)
      (cond
        ((record? op <wrap>)
         (pcombine env (unwrap op)
                   (map (lambda (arg) (peval env arg)) args)))
        ((code? op)
         (define result (emit-ins! 'combine env op args))
         (define! reg-info-effect (code-reg result) t)
         result)
        ((eq? (tag op) 'object)
         ;; TODO: handle partial static environment
         (combine env (lookup op 'compile) (cons op args)))
        (t (emit-ins! 'vm-error (list 'unapplicable op))))))

(define clone
    (lambda (env)
      (vecenv (parent env)
              (map (lambda (key) (list key (lookup env key)))
                   (keys env)))))

;; TODO: handle parent link
(define clone-into!
    (lambda (dst src)
      (for! (lambda (key)
              (define! dst key (lookup src key)))
            (keys src))))

(define save-psenv
    (lambda ()
      (map (lambda (env)
             (list env (clone env)))
           (keys psenv-table))))

(define restore-psenv!
    (lambda (save-list)
      (for! (lambda (el)
              (apply clone-into! el))
            save-list)))

;; Create the appropriate partial static environment store and
;; environment access code for compiling nested vau.  `pe-env' is the
;; environment component of the closure.

;; What this function does: Traverse `pe-env', for each partial static
;; environment encountered, mask every slot containing `<code>' from
;; compiling the outer vau with `%volatile-slots'.
(define psenv-import!
    (lambda (root-obj)
      (define process!
          (lambda (datum access-code)
            (cond
              ((eq? (tag datum) 'object)
               (when (bound? psenv-table datum)
                 (unless (bound? value-memo datum)
                   (define! value-memo datum (code-reg access-code))
                   (process! (parent datum) (emit-ins! 'parent datum))
                   (define volatile-slots nil)
                   (for!
                    (lambda (key)
                           (define value (lookup-local datum key '%broken-invariant))
                           (define! datum key
                             (process! value (emit-ins! 'lookup-local datum key '%broken-invariant))))
                    (keys datum))))
               datum)
              ((code? datum) access-code)
              ((eq? (tag datum) 'record)
               (define! value-memo datum (code-reg access-code))
               (define loop
                   (lambda (i)
                     (when (> i -1)
                       (cons (process! (record-field datum i)
                                       (emit-ins! 'record-field datum i))
                             (loop (- i 1))))))
               (apply record (cons (record-descriptor datum)
                                   (loop (- (lookup (record-descriptor datum) 'length) 1)))))
              (t datum))))
      (process! root-obj (record <code> 0))))

(define psenv-invalidate!
    (lambda (datum)
      (cond
        ((eq? (tag datum) 'object)
         (when (and (bound? psenv-table datum)
                    (not (eq? (parent datum) <closure>)))
           (for! (lambda (key)
                   (psenv-invalidate! (lookup datum key))
                   (define! datum key '%unknown))
                 (keys datum))))
        ((eq? (tag datum) 'record)
         (for! psenv-invalidate! (record-fields datum)))
        ((cons? datum)
         (psenv-invalidate! (car datum))
         (psenv-invalidate! (cdr datum))))))

;; Basically reverse `code-list' to get a instruction listing.
;; Perform dead-code elimination and compile remaining `vau' recursively.
(define collect-code-list
    (lambda (root-reg)
      (define mark-table (hashenv reg-info-effect (list (list root-reg t))))
      (define mark-ins
          (lambda (ins)
            (define class (car ins))
            (define body (cddr ins))
            (cond ((eq? class 'lit))
                  ((eq? class 'branch)
                   (define! mark-table (car body) t)
                   (map mark-ins (cdr (cadr body)))
                   (map mark-ins (cdr (caddr body))))
                  (t (map (lambda (reg) (define! mark-table reg t)) (cdr ins))))))
      (for! (lambda (ins)
              (when
                  (or (lookup-maybe mark-table (cadr ins) nil)
                      (and (eq? (car ins) 'define!)
                           (lookup-maybe mark-table (caddr ins) nil)))
                (mark-ins ins)))
            code-list)
      (for! (lambda (ins)
              (when
                  (or (lookup-maybe mark-table (cadr ins) nil)
                      (and (eq? (car ins) 'define!)
                           (lookup-maybe mark-table (caddr ins) nil)))
                (mark-ins ins)))
            code-list)
      (for! (lambda (ins)
              (when
                  (or (lookup-maybe mark-table (cadr ins) nil)
                      (and (eq? (car ins) 'define!)
                           (lookup-maybe mark-table (caddr ins) nil)))
                (mark-ins ins)))
            code-list)
      (define result (list (list 'reg root-reg)))
      (for! (lambda (ins)
              (when (lookup-maybe mark-table (cadr ins) nil)
                (if (eq? (car ins) 'vau)
                    (begin
                     (define value (lookup reg-info-value (cadr ins)))
                     (define saved-psenv-list (save-psenv))
                     (define compiled-body (do-compile value))
                     (restore-psenv! saved-psenv-list)
                     (push! result
                            (list* 'cvau (cadr ins) (caddr ins)
                                   compiled-body)))
                    (push! result ins))))
            code-list)
      result))

(define do-compile
    (lambda (f)
      ;; Returns a list of instructions.
      (print f)
      (with-fluids ((code-list nil)
                    (next-reg 3)
                    (psenv-table (hashenv psenv-table nil))
                    (value-memo (hashenv nil nil))
                    (reg-info-value (hashenv nil nil))
                    (reg-info-effect (hashenv nil nil)))
        (psenv-import! f)
        (define saved-compile (lookup f 'compile))
        (define! f 'compile (residualize-when (lambda _ t)))
        (define body (print (collect-code-list
                             (catch dead-branch-continuation
                               (reify
                                (combine (record <code> 1)
                                         (lookup f 'expand)
                                         (cons f (record <code> 2))))))))
        (define! f 'compile saved-compile)
        body)))

(define compile
    (lambda (f)
      (combine nil cvau (do-compile f))))

(define %volatile-slots '(*fluid-env*))

(define compile-install!
    (lambda (f)
      (when (record? f <wrap>)
        (define f (unwrap f)))
      (print f)
      (install-code! f (compile f))))

(for! compile-install!
      (list list cadr cddr caddr cdddr apply tag? cons? symbol? null? list* match-arglist
            lookup-slot call/cc invoke-continuation! <fluid> (lookup <fluid> 'setter) signal
            cata foldr foldl reverse append map filter for!
            code? dynamic-tail? list-dynamic? list-n-dynamic?
            record-fields all-keys nub remove member? reify emit-ins! bound? clone clone-into!
            plookup peval pcombine
            (lookup <primitive> 'expand) (lookup <closure> 'expand)
            (lookup <primitive> 'residualize) (lookup <closure> 'residualize)
            residualize-when
            #+nil (lookup if 'compile) (lookup begin2 'compile)
            (lookup (unwrap eval) 'compile) (lookup (unwrap combine) 'compile)
            #+nil collect-code-list #+nil psenv-import!
            psenv-invalidate!
            call-with-fluids))

#+nil (define for-env!
    (lambda (f env)
      (define mark-table (hashenv nil nil))
      (define process!
          (lambda (env)
            (cond
              ((eq? (tag env) 'wrap)
               (process! (unwrap env)))
              ((eq? (tag env) 'object)
               (unless (bound? mark-table env)
                 (define! mark-table env t)
                 (f env)
                 (process! (parent env))
                 (for! (lambda (key)
                         (process! (lookup-local env key nil)))
                       (keys env)))))))
      (process! env)))

#+nil (for-env!
 (lambda (f)
   (when (eq? (parent f) <closure>)
     (print f)
     (install-code! f (compile f))))
 (the-environment))

(define is?
    (lambda (object prototype)
      (and object (eq? (tag object) 'object)
           (or (eq? object prototype)
               (is? (parent object) prototype)))))

#+nil (for! (lambda (applicative)
        (print (unwrap applicative))
        (install-code! (unwrap applicative)
                       (compile (unwrap applicative))))
      (list foldl reverse map))

#+nil (define match-arglist1
    (wrap (vau0 _ args
                (if (cons? (car args))
                    (cons (list (car (car args)) (car (cadr args)))
                          (match-arglist (cdr (car args)) (cdr (cadr args))))
                    (if (symbol? (car args))
                        (list args)
                        nil)))))
#+nil (define! (unwrap match-arglist1) 'compile expand-always)
#+nil (print (pcombine nil (unwrap match-arglist1) (list '(x) (vecenv <code> (list (list 'reg -1))))))
#+nil (define f (wrap (vau0 _ x (if (cons? (cdr x)) (cons (car x) (apply f (cdr x))) (car x)))))
#+nil (define! (unwrap f) 'compile expand-when-arglist)
#+nil (print (compile (unwrap f)))
