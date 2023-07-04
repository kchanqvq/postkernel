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

(define reverse
    (lambda (a-list)
      (foldl (lambda (result el) (cons el result)) nil a-list)))

(define map
    (lambda (f a-list)
      (reverse
       (foldl (lambda (rest el) (cons (f el) rest))
              nil a-list))))

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
      (map (lambda (binding)
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


(define is?
    (lambda (object prototype)
      (and object (eq? (tag object) 'object)
           (or (eq? object prototype)
               (is? (parent object) prototype)))))

(define <code> (vecenv nil nil))

(define code-list nil)
(define next-reg nil)
(define env-store nil)
(define value-memo nil)

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
                  (t (map (lambda (reg) (define! mark-table reg t)) body)))))
      (define result (list (list 'reg root-reg)))
      (define process
          (lambda (code-list)
            (when code-list
              (define ins (car code-list))
              (when (or (eq? (car ins) 'combine)
                        (eq? (car ins) 'define!)
                        (eq? (car ins) 'mutate!)
                        (bound? mark-table (cadr ins)))
                (mark-ins ins)
                (push! result ins))
              (process (cdr code-list)))))
      (process code-list)
      result))

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
                  (if (is? args <code>)
                      (lookup op 'residualize)
                      (lookup op 'expand))
                  (cons op args))))

(define expand-when-static
    (vau env (op . args)
         (combine env
                  (if (or (is? args <code>)
                          (any? (lambda (arg) (is? arg <code>)) args))
                      (lookup op 'residualize)
                      (lookup op 'expand))
                  (cons op args))))

(define! <code> 'compile
  (vau env (op . args)
       (emit-ins! 'combine env op args)))
(define! <primitive> 'compile residualize-always)
(define! <closure> 'compile expand-when-static)

(define! quote 'compile expand-when-arglist)
(define! (unwrap list*) 'compile expand-always)

(map (lambda (applicative)
       (define! (unwrap applicative) 'compile expand-when-arglist))
     (list cons wrap
           list cadr cddr caddr apply tag? cons? symbol? null?
           match-arglist
           not install-bindings!))

(map (lambda (primitive-app)
       (define! (unwrap primitive-app) 'compile expand-when-static))
     (list car cdr unwrap tag eq?))

(define! if 'compile
  (vau env (_ test then else)
       (define test (peval env test))
       (cond ((is? test <code>)
              (define reg next-reg)
              (inc! next-reg 1)
              (push! code-list
                     (list 'branch reg (reify test)
                           ;; TODO: handle env-store correctly
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
  (vau env (_ x) (print x) x))
(define! (unwrap eval) 'compile (vau _ (_ env form) (peval env form)))
(define! (unwrap combine) 'compile  (vau _ (_ env op args) (pcombine env op args)))

(define! (unwrap vecenv) 'compile
  (vau _ (_ parent alist)
       (define parent-reg (reify parent))
       (define code (emit-ins! 'vecenv (vecenv <code> (list (list 'reg parent-reg))) alist))
       (define! env-store (lookup code 'reg)
         (vecenv (if parent (lookup env-store parent-reg) parent) alist))
       code))
(define! (unwrap define!) 'compile
  (vau _ (_ env key value)
       (define reg (reify env))
       (emit-ins! 'define! (vecenv <code> (list (list 'reg reg))) key value)
       (define! (lookup env-store reg) key value)))
;; TODO: call compile recursively
(define! vau0 'compile
  (vau env (_ . args)
       (define env-reg (reify env))
       (define code (emit-ins! 'vau (vecenv <code> (list (list 'reg env-reg))) args))
       (define! env-store (lookup code 'reg)
         (combine (if env (lookup env-store env-reg) env) vau0 args))
       code))

(define reify
    (lambda (value)
      (if (bound? value-memo value)
          (lookup value-memo value)
          (define! value-memo value
            (cond
              ((cons? value)
               (reify (emit-ins! 'cons (car value) (cdr value))))
              ((eq? (tag value) 'wrap)
               (reify (emit-ins! 'wrap (unwrap value))))
              ((is? value <code>)
               (lookup value 'reg))
              (t
               (define reg next-reg)
               (inc! next-reg 1)
               (push! code-list (list 'lit reg value))
               (when (eq? (tag value) 'object)
                 (define! env-store reg value))
               reg))))))

(define emit-ins!
    (lambda (ins . args)
      (define args (map reify args))
      (define reg next-reg)
      (inc! next-reg 1)
      (push! code-list (list* ins reg args))
      (vecenv <code> (list (list 'reg reg)))))

(define lookup-maybe
    (lambda (env x default)
      (if (bound? env x)
          (lookup env x)
          default)))

(define plookup
    (lambda (env key)
      (if (is? env <code>)
          (let ((store-info (lookup-maybe env-store (lookup env 'reg) nil)))
            (if (bound? store-info key)
                (lookup store-info key)
                (emit-ins! 'lookup env key)))
          (lookup env key))))

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
         (define effective-op
             (if (is? op <code>)
                 (lookup-maybe env-store (lookup op 'reg) op)
                 op))
         (combine env (lookup effective-op 'compile) (cons effective-op args)))
        (t (emit-ins! 'error)))))

(define compile
    (lambda (f)
      (fluid-let! ((code-list nil)
                   (next-reg 3)
                   (env-store (hashenv nil nil))
                   (value-memo (hashenv nil (list (list f 0)))))
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
                  (combine nil cvau (print body)))))

(map (lambda (applicative)
       (print (unwrap applicative))
       (install-code! (unwrap applicative)
                      (compile (unwrap applicative))))
     (list list cadr cddr caddr cdddr apply tag? cons? symbol? null? list* match-arglist
           cata foldr foldl reverse map is?))

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
