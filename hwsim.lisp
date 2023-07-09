(defpackage #:pk/hwsim
  (:use #:cl)
  (:shadow #:eval))
(in-package #:pk/hwsim)
(defstruct (wrap (:constructor wrap (operative))) (operative))
(defstruct residual (term))
(defun unwrap (x) (wrap-operative x))
(defun tag (x)
  (typecase x
    (cons 'cons)
    ((eql _) '_)
    (null 'null)
    (symbol 'symbol)
    (fixnum 'fixnum)
    (wrap 'wrap)
    (vector 'object)))

(defmacro id (x) `(aref ,x 0))
(defmacro parent (x) `(aref ,x 1))
(defmacro keyvec (x) `(aref ,x 2))
(defmacro value (x i) `(aref ,x (+ 3 ,i)))

(defun vecenv (parent list)
  (let ((s (length list)))
    (make-array (+ 3 s)
                :fill-pointer (+ 3 s)
                :adjustable t
                :initial-contents
                (list* 'vecenv parent
                       (make-array s :fill-pointer s
                                     :adjustable t
                                     :initial-contents (mapcar #'car list))
                       (mapcar #'cadr list)))))

(defun hashenv (parent list)
  (let ((table (make-hash-table :test 'equal)))
    (mapc (lambda (binding)
            (setf (gethash (car binding) table) (cadr binding)))
          list)
    (make-array 3 :fill-pointer 3 :adjustable t
                  :initial-contents
                  (list 'hashenv parent table))))

(defvar <closure> (vecenv nil nil))
(defvar <primitive> (vecenv nil nil))

(defun lookup-default (env x default)
  (let ((value (lookup-local env x default)))
    (if (eq value default)
        (if env (lookup-default (parent env) x default) default)
        value)))

(defun lookup (env x)
  (let ((value (lookup-default env x '%%unbound)))
    (if (eq value '%%unbound)
        (error "Unbound key ~A." x)
        value)))

(defun lookup-local (env x default)
  (ecase (tag env)
    ((object)
     (ecase (id env)
       ((vecenv)
        (let ((p (position x (keyvec env) :test 'equal)))
          (if p (value env p) default)))
       ((hashenv)
        (multiple-value-bind (value boundp)
            (gethash x (aref env 2))
          (if boundp value default)))))
    ((null) default)))

(defun keys (env)
  (ecase (tag env)
    ((object)
     (ecase (id env)
       ((vecenv) (map 'list #'identity (keyvec env)))
       ((hashenv)
        (loop for k being each hash-key of (aref env 2)
              collect k))))))

(defun define! (env x y)
  (ecase (tag env)
    ((object)
     (ecase (id env)
       ((vecenv)
        (let ((p (position x (keyvec env) :test 'equal)))
          (if p (setf (value env p) y)
              (progn
                (vector-push-extend x (keyvec env))
                (vector-push-extend y env)
                y))))
       ((hashenv)
        (setf (gethash x (aref env 2)) y))))))

(defun mutate! (env x y)
  (ecase (tag env)
    ((object)
     (ecase (id env)
       ((vecenv)
        (let ((p (position x (keyvec env) :test 'equal)))
          (if p (setf (value env p) y)
              (mutate! (parent env) x y))))
       ((hashenv)
        (if (nth-value 1 (gethash x (aref env 2)))
            (setf (gethash x (aref env 2)) y)
            (mutate! (parent env) x y)))))))

(defun eval (env form)
  (case (tag form)
    ((cons)
     (combine env (eval env (car form)) (cdr form)))
    ((symbol) (lookup env form))
    (t form)))

(defun combine (env op args)
  (ecase (tag op)
    ((wrap)
     (combine env (unwrap op) (mapcar (lambda (arg) (eval env arg)) args)))
    ((object)
     (funcall (value op 0) op env args))))

(defun vau (lexenv args)
  (assert (cddr args))
  (assert (not (cdddr args)))
  (vecenv <closure>
          (list
           (list 'code
                 (lambda (self env args &aux alist)
                   (let ((envf (value self 2))
                         (argsf (value self 3))
                         (expr (value self 4)))
                     (unless (eq envf '_) (push (list envf env) alist))
                     (unless (eq argsf '_) (push (list argsf args) alist))
                     (eval (vecenv (value self 1) alist) expr))))
           (list 'env lexenv)
           (list 'env-formal (car args))
           (list 'args-formal (cadr args))
           (list 'expr (caddr args)))))

(defun cvau (lexenv args)
  (declare (ignore lexenv))
  (let ((reg-symbols (make-hash-table)))
    (setf (gethash 0 reg-symbols) '%self
          (gethash 1 reg-symbols) '%env
          (gethash 2 reg-symbols) '%args)
    (labels ((reg-symbol (n)
               (or (gethash n reg-symbols)
                   (setf (gethash n reg-symbols) (make-symbol (format nil "R~A" n)))))
             (process-form (form)
               (let ((dest (cadr form))
                     (rest (cddr form)))
                 `(,(reg-symbol dest)
                   ,(case (car form)
                      ((lit)
                       `',(car rest))
                      ((branch)
                       (let ((test (car rest))
                             (then (cadr rest))
                             (else (caddr rest)))
                         `(if ,(reg-symbol test)
                              ,(process-begin then)
                              ,(process-begin else))))
                      ((cvau)
                       `(vecenv <closure>
                                (list (list 'code
                                            (lambda (%self %env %args)
                                              ,(process (cdr rest))))
                                      (list 'env ,(reg-symbol (car rest))))))
                      (t
                       `(,(car form) ,@(mapcar #'reg-symbol rest)))))))
             (process (body)
               (let ((bindings (mapcar #'process-form (butlast body)))
                     (tail
                       (let ((form (car (last body))))
                         (ecase (car form)
                           ((reg) (reg-symbol (cadr form)))))))
                 (if (eq tail (caar (last bindings)))
                     `(let* ,(butlast bindings) ,(cadar (last bindings)))
                     `(let* ,bindings ,tail))))
             (process-begin (form)
               (ecase (car form)
                 ((begin) (process (cdr form))))))
      (let ((sb-ext:*muffled-warnings* 'sb-int:simple-style-warning))
          (vecenv <closure>
               (list (list 'code (compile nil `(lambda (%self %env %args)
                                                 ,(process args))))))))))

(defun install-code! (vau cvau)
  (setf (value vau 0) (value cvau 0))
  t)

(defun make-primop (f)
  (let ((lambda-name (intern (format nil "%~A" (symbol-name f)))))
    (vecenv <primitive>
            (list (list 'code (cl:eval `(labels ((,lambda-name (self env args)
                                                   (declare (ignore self))
                                                   (,f env args)))
                                          #',lambda-name)))
                  (list 'name f)))))

(defun make-primapp (f)
  (let ((lambda-name (intern (format nil "%~A" (symbol-name f)))))
    (wrap
     (vecenv <primitive>
             (list (list 'code (cl:eval `(labels ((,lambda-name (self env args)
                                                    (declare (ignore self env))
                                                    (apply #',f args)))
                                           #',lambda-name)))
                   (list 'name f))))))

(defun %if (env args)
  (if (eval env (car args))
      (eval env (cadr args))
      (eval env (caddr args))))
(defun %time (env args)
  (time (eval env (car args))))
(defun %parent (x) (parent x))
(defun %id (x) (id x))

(defvar *inspecting-object* nil)

(defun %inspect (x) (setq *inspecting-object* x))

(defun boot ()
  (let ((env
          (hashenv nil `((vau0 ,(make-primop 'vau))
                        (cvau ,(make-primop 'cvau))
                        #+nil (ins ,#'ins) #+nil (lit ,#'lit)
                        (<closure> ,<closure>)
                        (<primitive> ,<primitive>)
                        (if ,(make-primop '%if))
                        (eq? ,(make-primapp 'equal))
                        ,@ (mapcar (lambda (symbol) `(,symbol ,(make-primapp symbol)))
                                   '(eval combine define! mutate!
                                     tag cons car cdr wrap unwrap > = < + - * /
                                     vecenv hashenv keys print break error
                                     lookup lookup-local lookup-default
                                     install-code!))
                         (parent ,(make-primapp '%parent))
                         (id ,(make-primapp '%id))
                        (time ,(make-primop '%time))
                        (inspect ,(make-primapp '%inspect))
                        (nil nil)
                        (t t))))
        (*print-circle* t))
    (time (dolist (form (uiop:read-file-forms "boot.k"))
       (when (equal form '(**break**)) (return))
       (eval env form)))
    (handler-case
        (loop
          (format t "~&PK> ")
          (print (eval env (read))))
            (end-of-file () (format t "~%Moriturus te saluto.")))
    #+nil (prin1 (time (eval env '(fib 10))))))

(defun fib (x)
  (cond ((> x 1) (+ (fib (- x 1)) (fib (- x 2))))
        (t 1)))
#+nil (reify (m/eval (vector 'closure nil (lambda (_self _cont _env arg) arg)) *env* '(vau _ (x) (let ((y x)) y))))
#+nil (m/eval *halt* *env* `((vau1 _ (_ x) x) . ,(reflect 'x)))
#+nil (vau1 e0 (e args . body)
      (eval (list vau (eval (reflect e) (cons (eval e0 (list* vau1 e args body)) (reflect x))))))
