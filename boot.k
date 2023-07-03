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
      (foldr (lambda (kar kdr) (cons (f kar) kdr))
             nil a-list)))

(define let
    (vau env (bindings . body)
         (eval env
               (cons (list* lambda (map car bindings) body)
                     (map cadr bindings)))))

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

(define and
    (vau env args
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
(define next-reg 2)
(define env-store nil)
(define value-memo nil)

(define! <primitive> 'compile
  (vau env (op . args)
       (apply emit-ins! (cons (lookup op 'name) args))))
(define! <closure> 'compile
  (vau env (op . args)
       (emit-ins! 'combine env op args)))
(define! <code> 'compile
  (vau env (op . args)
       (emit-ins! 'combine env op args)))

(define! <primitive> 'expand
  (vau env (op . args) (combine nil op args)))
(define! <closure> 'expand
  (vau env (op . args)
       (peval (pcombine
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

(define expand-when-arglist
    (vau env (op . args)
         (combine env
                  (if (is? args <code>)
                      (lookup (parent op) 'compile)
                      (lookup op 'expand))
                  (cons op args))))

(define expand-when-static
    (vau env (op . args)
         (combine env
                  (if (any? (lambda (arg) (is? arg <code>)) args)
                      (lookup (parent op) 'compile)
                      (lookup op 'expand))
                  (cons op args))))

(define! quote 'compile expand-when-arglist)
(define! (unwrap list*) 'compile expand-always)

(map (lambda (applicative)
       (define! (unwrap applicative) 'compile expand-when-arglist))
     (list cons
           list cadr cddr caddr apply tag? cons? symbol? null?
           match-arglist
           not install-bindings!))

(map (lambda (operative)
       (define! operative 'compile expand-when-arglist))
     (list vau1 let begin2 begin vau2 cond when unless
           and or
           push! inc! fluid-let!))

(map (lambda (f)
       (define! (unwrap f) 'compile expand-when-static))
     (list car cdr tag eq?))

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
                                        (value-memo (vecenv value-memo nil)))
                                       (push! code-list
                                              (list 'reg (reify (peval env then))))
                                       (cons 'begin (reverse code-list)))
                           (fluid-let! ((next-reg next-reg)
                                        (code-list nil)
                                        (value-memo (vecenv value-memo nil)))
                                       (push! code-list
                                              (list 'reg (reify (peval env else))))
                                       (cons 'begin (reverse code-list)))))
              (vecenv <code> (list (list 'reg reg))))
             (test (peval env then))
             (t (peval env else)))))
(define! (unwrap eval) 'compile (vau _ (_ env form) (peval env form)))
(define! (unwrap combine) 'compile  (vau _ (_ env op args) (pcombine env op args)))

(define! (unwrap vecenv) 'compile
  (vau _ (_ parent alist)
       (define parent-reg (reify parent))
       (define code (emit-ins! 'vecenv (vecenv <code> (list (list 'reg parent-reg))) alist))
       (define! env-store (lookup code 'reg) (vecenv (lookup env-store parent-reg) alist))
       code))
(define! (unwrap define!) 'compile
  (vau _ (_ env key value)
       (define reg (reify env))
       (emit-ins! 'define! (vecenv <code> (list (list 'reg reg))) key value)
       (define! (lookup env-store reg) key value)))

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
      (push! code-list (list* 'ins reg ins args))
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
         (combine env (lookup op 'compile) (cons op args)))
        (t (emit-ins! 'error)))))

(define compile
    (lambda (f)
      (fluid-let! ((code-list nil)
                   (next-reg 2)
                   (env-store (vecenv nil nil))
                   (value-memo (vecenv nil nil)))
                  (define saved-compile (lookup f 'compile))
                  (define! f 'compile (lookup (parent f) 'compile))
                  (push! code-list
                         (list 'reg
                               (reify
                                (combine (vecenv <code> (list (list 'reg 0)))
                                         (lookup f 'expand)
                                         (cons f (vecenv <code> (list (list 'reg 1))))))))
                  (define! f 'compile saved-compile)
                  (list* 'cvau 'env 'args
                         (reverse code-list)))))

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
