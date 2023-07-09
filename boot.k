;; -*- mode: Lisp-*-
(define! ((vau0 e _ e)) ((vau0 _ x x) . define)
  (vau0 e args (define! e (car args) (eval e (car (cdr args))))))
(define vau vau0)
(define the-environment (vau0 e _ e))
(define lambda
    (vau env args
         (wrap (eval env (cons vau (cons _ args))))))
(define list (lambda x x))
(define quote (vau _ x (car x)))
(define cadr (lambda args (car (cdr (car args)))))
(define cddr (lambda args (cdr (cdr (car args)))))
(define caddr (lambda args (car (cddr (car args)))))
(define cdddr (lambda args (cdr (cddr (car args)))))
(define apply (wrap (vau env args (combine env (unwrap (car args)) (cadr args)))))

(define tag? (lambda x (eq? (tag (car x)) (cadr x))))
(define cons? (lambda x (eq? (tag (car x)) 'cons)))
(define symbol? (lambda x (eq? (tag (car x)) 'symbol)))
(define null? (lambda x (eq? (tag (car x)) 'null)))

(define list* (lambda x (if (cons? (cdr x)) (cons (car x) (apply list* (cdr x))) (car x))))

(define match-arglist
    (lambda args
      (if (cons? (car args))
          (if (eq? (car (car args)) _)
              (match-arglist (cdr (car args)) (cdr (cadr args)))
              (cons (list (car (car args)) (car (cadr args)))
                    (match-arglist (cdr (car args)) (cdr (cadr args)))))
          (if (symbol? (car args))
              (list args)
              nil))))

;; Arglist pattern matching
(define vau1
    (vau0 env0 args0
         (vau0 env args
               (eval (vecenv env0 (match-arglist (cons (car args0) (cadr args0)) (cons env args)))
                     (caddr args0)))))
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

(define compile-print (lambda (x) x))

(define let
    (vau env (bindings . body)
         (combine (vecenv env
                          (map (lambda (binding)
                                 (list (car binding)
                                       (eval env (cadr binding))))
                               bindings))
                  begin body)))

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

(define and
    (vau0 env args
         (if (cons? args)
             (let ((head (eval env (car args))))
               (when head
                 (if (cons? (cdr args))
                     (combine env and (cdr args))
                     head)))
             t)))

(define or
    (vau env args
         (if (cons? args)
             (let ((head (eval env (car args))))
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

(define install-bindings!
    (lambda (env bindings)
      (for! (lambda (binding)
              (mutate! env (car binding) (cadr binding)))
            bindings)))

(define fluid-let!
    (vau env (bindings . body)
         (define saved-bindings
             (map (lambda (binding)
                    (list (car binding) (lookup env (car binding))))
                  bindings))
         (define new-bindings
             (map (lambda (binding)
                    (list (car binding) (eval env (cadr binding))))
                  bindings))
         (install-bindings! env new-bindings)
         (define result (combine env begin body))
         (install-bindings! env saved-bindings)
         result))


(define <code> (vecenv nil nil))
(define code?
    (lambda (object)
      (and (eq? (tag object) 'object)
           (eq? (parent object) <code>))))

(define code-list nil)
(define next-reg nil)
;; `env-store' is the store data structure for partial evaluation.

;; Consider in dynamic semantics, Env: Var -> (Env + OtherVal...)  To
;; make it mutable, factor it into Env: Var -> Loc, Store: Loc -> (Env
;; + OtherVal...)  Now let Loc = Reg and we have Env: Var -> Reg,
;; Store: Reg -> (Env + OtherVal...)

;; This is almost what we use for PEval time environments and
;; `env-store', except that we don't allocate Reg for every
;; environment, i.e. actually Loc = Reg + StaticLoc.  The environments
;; that are not (yet) side-effected by PEval-ed code are not assigned
;; Reg. They are represented by themselves directly, i.e.  Env : Var
;; -> (Reg + StaticEnv), Store: Reg -> (Env + OtherVal...).  Note that
;; some StaticEnv in Env objects may later be assigned a Reg and
;; side-effected upon. These StaticEnv occurrences are not
;; automatically back-patched, so always normalize a PEval time
;; environment (something like (lookup env-store (reify env))) to get
;; the update-to-date PEval time state.
(define env-store nil)
(define value-memo nil)

(define! <primitive> 'residualize
  (vau env (op . args)
       (apply emit-ins! (cons (lookup op 'name) args))))
(define! <closure> 'residualize
  (vau env (op . args)
       (emit-ins! 'combine env op args)))

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

(define expand-always
    (vau env (op . args)
         (combine env (lookup op 'expand) (cons op args))))

(define residualize-always
    (vau env (op . args)
         (combine env (lookup op 'residualize) (cons op args))))

(define expand-when-arglist
    (vau env (op . args)
         (combine env
                  (if (code? args)
                      (lookup op 'residualize)
                      (lookup op 'expand))
                  (cons op args))))

(define expand-when-static
    (vau env (op . args)
         (combine env
                  (if (or (code? args)
                          (any? (lambda (arg) (code? arg)) args))
                      (lookup op 'residualize)
                      (lookup op 'expand))
                  (cons op args))))

(define expand-when-nth-static
    (lambda (n)
      (vau env (op . args)
           (combine env
                    (if (or (code? args)
                            (code? (nth args n)))
                        (lookup op 'residualize)
                        (lookup op 'expand))
                    (cons op args)))))

(define! <code> 'compile
  (vau env (op . args)
       (emit-ins! 'combine env op args)))
(define! <primitive> 'compile residualize-always)
(define! <closure> 'compile expand-when-static)

(define! quote 'compile expand-when-arglist)
(define! (unwrap list*) 'compile expand-always)

(for! (lambda (applicative)
        (define! (unwrap applicative) 'compile expand-when-arglist))
      (list cons wrap
            list cadr cddr caddr apply tag? cons? symbol? null?
            not install-bindings!))

(define! (unwrap match-arglist) 'compile (expand-when-nth-static 0))

(for! (lambda (primitive-app)
        (define! (unwrap primitive-app) 'compile expand-when-static))
      (list car cdr unwrap tag eq?))

(define! if 'compile
  (vau env (_ test then else)
       (define test (peval env test))
       (cond ((code? test)
              (define reg next-reg)
              (inc! next-reg 1)
              (push! code-list
                     (list 'branch reg (reify test)
                           ;; TODO: handle `env-store' merge correctly
                           (fluid-let! ((next-reg next-reg)
                                        (code-list nil)
                                        (value-memo (hashenv value-memo nil)))
                                       (cons 'begin (collect-code-list (reify (peval env then)))))
                           (fluid-let! ((next-reg next-reg)
                                        (code-list nil)
                                        (value-memo (hashenv value-memo nil)))
                                       (cons 'begin (collect-code-list (reify (peval env else)))))))
              (vecenv <code> (list (list 'reg reg))))
             (test (peval env then))
             (t (peval env else)))))

(define! begin2 'compile
  (vau env (_ first second)
       (peval env first)
       (peval env second)))
(define! (unwrap compile-print) 'compile
  (vau env (_ x) (print code-list) (print x) x))
(define! (unwrap eval) 'compile (vau _ (_ env form) (peval env form)))
(define! (unwrap combine) 'compile  (vau _ (_ env op args) (pcombine env op args)))

(define! (unwrap vecenv) 'compile
  (vau _ (_ parent alist)
       (define code (emit-ins! 'vecenv parent alist))
       (if (code? alist) code
           (begin
            (define result (vecenv parent alist))
            (define! value-memo result (reify code))
            (define! env-store result (vecenv nil (list (list 'dynamic? t))))
            result))))

(define! (unwrap define!) 'compile
  (vau _ (_ env key value)
       (emit-ins! 'define! env key value)
       (unless (bound? env-store env)
         (define! env-store env (vecenv nil nil)))
       (define! (lookup env-store env) key value)))
;; TODO: call compile recursively
;; The following do not compile nested vau, i.e. closures are
;; interpreted for now.  Our `compile' will look for remaining
;; closures after dead-code elimination and compile them recursively,
;; so we don't bother compiling `vau's that are only used during
;; expansion.
(define! vau0 'compile
  (vau env (_ . args)
       (define result (combine env vau0 args))
       (define! value-memo result (reify (emit-ins! 'vau env args)))
       (annotate-ins! env args)
       result))

(define reify
    (lambda (value)
      (lookup-maybe
       value-memo value
       (define! value-memo value
         (cond
           ((cons? value)
            (reify (emit-ins! 'cons (car value) (cdr value))))
           ((eq? (tag value) 'wrap)
            (reify (emit-ins! 'wrap (unwrap value))))
           ((code? value)
            (lookup value 'reg))
           (t
            (define reg next-reg)
            (inc! next-reg 1)
            (push! code-list (list 'lit reg value))
            (when (eq? (tag value) 'object)
              (define! env-store value
                (vecenv nil
                        (map (lambda (slot) (list slot '%unknown))
                             (lookup-maybe value '%volatile-slots nil)))))
            reg))))))

(define emit-ins!
    (lambda (ins . args)
      (define args (map reify args))
      (define reg next-reg)
      (inc! next-reg 1)
      (push! code-list (list* ins reg args))
      (vecenv <code> (list (list 'reg reg)))))

(define annotate-ins!
    (lambda annotations
      (set! code-list (cons (append (car code-list) annotations)
                            (cdr code-list)))))

(define lookup-maybe
    (vau dynenv (env x default)
         (define result (lookup-default (eval dynenv env) (eval dynenv x) '%unbound))
         (if (eq? result '%unbound) (eval dynenv default) result)))

(define bound?
    (lambda (env key)
      (not (eq? (lookup-default env key '%unbound) '%unbound))))

(define plookup
    (lambda (env key)
      (when env
        (define store-info (lookup-maybe env-store env nil))
        (define store-value (lookup-local store-info key '%unbound))
        (if (eq? store-value '%unbound)
            (begin
             (define value (lookup-local env key '%unbound))
             (if (eq? value '%unbound)
                 (plookup (parent env) key)
                 value))
            (if (eq? store-value '%unknown)
                (emit-ins! 'lookup env key)
                store-value)))))

(define peval
    (lambda (env form)
      (cond ((cons? form)
             (pcombine env (peval env (car form)) (cdr form)))
            ((symbol? form) (plookup env form))
            (t form))))

(define pcombine
    (lambda (env op args)
      (cond
        ((eq? (tag op) 'wrap)
         (pcombine env (unwrap op)
                   (map (lambda (arg) (peval env arg)) args)))
        ((eq? (tag op) 'object)
         ;; TODO: handle `env-store'
         (combine env (lookup op 'compile) (cons op args)))
        (t (emit-ins! 'error)))))

(define all-keys
    (lambda envs
      (define table (hashenv nil nil))
      (define process!
          (lambda (env)
            (when env
              (for! (lambda (key) (define! table key t))
                    (keys env))
              (process! (parent env)))))
      (for! process! envs)
      (keys table)))


;; Create the appropriate `env-store' entry and environment access
;; code for compiling nested vau.  `pe-env' is the environment
;; component of the closure being compiled and `old-env-store' is the
;; `env-store' for compiling the outer vau.

;; What this function does: Traverse `pe-env', for each environment
;; encountered, create `env-store' entry inheriting from corresponding
;; `old-env-store' and mask every slot containing `<code>' from
;; compiling the outer vau with `%unknown'. The traversal only
;; descends into environments with `dynamic?'=t in `old-env-store'.
(define env-store-import!
  (lambda (pe-env old-env-store)
    (define process-env!
        (vau dynenv (env-expr emit-ins-expr)
             (define env (eval dynenv env-expr))
             (when env
               (define! value-memo env (reify (eval dynenv emit-ins-expr)))
               (process-env! (parent env) (emit-ins! 'parent env))
               (define store-info (lookup-maybe old-env-store env nil))
               (define! env-store env
                 (vecenv store-info
                         (foldr (lambda (key rest)
                                  (define value
                                      (lookup-maybe store-info key (lookup env key)))
                                  (if (code? value) ;; TODO: traverse value types recursively.
                                      (begin
                                       (define new-code (emit-ins! 'lookup env key))
                                       (define! value-memo value (reify new-code))
                                       (cons (list key new-code) rest))
                                      (begin
                                       (when (eq? (tag value) 'object)
                                         (process-env! value (emit-ins! 'lookup env key)))
                                       rest)))
                                nil
                                (if (lookup-maybe store-info 'dynamic? nil)
                                    (all-keys store-info env)
                                    (all-keys store-info))))))))
    (process-env! pe-env (emit-ins! 'lookup (vecenv <code> (list (list 'reg 0))) 'env))))

;; Basically reverse `code-list' to get a instruction listing.
;; Perform dead-code elimination and compile remaining `vau' recursively.
(define collect-code-list
    (lambda (root-reg)
      (define mark-table (hashenv nil (list (list root-reg t))))
      (define mark-ins
          (lambda (ins)
            (define class (car ins))
            (define body (cddr ins))
            (cond ((eq? class 'lit))
                  ((eq? class 'branch)
                   (define! mark-table (car body) t)
                   (map mark-ins (cdr (cadr body)))
                   (map mark-ins (cdr (caddr body))))
                  ((eq? class 'reg)
                   (define! mark-table (cadr ins) t))
                  (t (map (lambda (reg) (define! mark-table reg t)) body)))))
      (define result (list (list 'reg root-reg)))
      (define process!
          (lambda (a-code-list)
            (when a-code-list
              (define ins (car a-code-list))
              (when (or (eq? (car ins) 'combine)
                        (eq? (car ins) 'define!)
                        (eq? (car ins) 'mutate!)
                        (eq? (car ins) 'branch) ;; TODO: eliminate pure `branch'
                        (bound? mark-table (cadr ins)))
                (mark-ins ins)
                (if (eq? (car ins) 'vau)
                    (begin
                     (define annotations (cddr (cddr ins)))
                     (define old-env-store env-store)
                     (define compiled-body
                         (fluid-let! ((code-list nil)
                                      (next-reg 3)
                                      (env-store (hashenv nil nil))
                                      (value-memo (hashenv nil nil)))
                                     (env-store-import! (car annotations) old-env-store)
                                     (define f (combine (car annotations) vau0 (cadr annotations)))
                                     (define! value-memo f 0)
                                     (do-compile f)))
                     (push! result
                            (list* 'cvau (cadr ins) (caddr ins)
                                   compiled-body)))
                    (push! result ins)))
              (process! (cdr a-code-list)))))
      (process! code-list)
      result))

(define do-compile
    (lambda (f)
      (print f)
      (define saved-compile (lookup f 'compile))
      (define! f 'compile
        (vau env (op . args)
             (emit-ins! 'combine env (vecenv <code> (list (list 'reg 0))) args)))
      (define body (collect-code-list
                    (reify
                     (combine (vecenv <code> (list (list 'reg 1)))
                              (lookup f 'expand)
                              (cons f (vecenv <code> (list (list 'reg 2))))))))
      (define! f 'compile saved-compile)
      (print body)))

(define compile
    (lambda (f)
      (fluid-let! ((code-list nil)
                   (next-reg 3)
                   (env-store (hashenv nil nil))
                   (value-memo (hashenv nil (list (list f 0)))))
                  (combine nil cvau (do-compile f)))))

(define %volatile-slots '(code-list next-reg env-store value-memo))

(for! (lambda (f)
        (when (eq? (tag f) 'wrap)
          (define f (unwrap f)))
        (print f)
        (install-code! f (compile f)))
      (list list cadr cddr caddr cdddr apply tag? cons? symbol? null? list* match-arglist
            cata foldr foldl reverse append map for! bound? code?
            reify emit-ins! plookup peval pcombine
            #+nil collect-code-list
            (lookup <primitive> 'expand)
            (lookup <closure> 'expand)
            (lookup <primitive> 'residualize)
            (lookup <closure> 'residualize)
            expand-always residualize-always expand-when-arglist
            expand-when-static expand-when-nth-static))
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

#+nil (define is?
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
