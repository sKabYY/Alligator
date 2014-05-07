#lang racket

; Expression = Variable
;            | Number
;            | Boolean
;            | (lambda (Variable*) Expression)
;            | (letrec ((Variable Expression)*) Expression)
;            | (begin Expression*)
;            | (set! Variable Expression)
;            | (letcc Variable Expression)
;            | (raise Expression)
;            | (catch Expression with Variable Expression)
;            | (Expression Expression*)
;
; Value = Number
;       | Boolean
;       | Closure
;       | Opd
;       | <void>
;       | Mutpair
;       | Continuation
;
; Closure: (Variable*) * Expression * Environment
; Mutpair: Reference * Reference
;
; Opd:
;  ifv: Boolean * T * T -> T
;  +: Number * Number * ... -> Number
;  -: Number * Number * ...-> Number
;  *: Number * Number * ...-> Number
;  remainder: Number * Number * ...-> Number
;  zero?: Number -> Boolean
;  print: Value -> <void>
;  pair: Value * Value -> Mutpair
;  mutpair?: Value -> Boolean
;  left: Mutpair -> Value
;  right: Mutpair -> Value
;  setleft!: Mutpair * Value -> <void>
;  setright!: Mutpair * Value -> <void>
;
; (if L M N)
; = ((ifv L (lambda () M) (lambda () N)))
;
; (let ((X1 N1)...(Xn Nn)) M)
; = ((lambda (X1...Xn) M) N1...Nn)
;
; (fix Xf (X1...Xn) M)
; = (letrec ((X1 (lambda (X1...Xn) M))) X1)
;
; (cc M N)
; = (M N)
;
; Environment: Variable -> Reference
; Store: Reference -> Value

(provide interp)
(define the-max-store-size 32)
(define (interp exp1)
  (initialize-store! the-max-store-size)
  (value-of/k (macro-translate exp1) (init-env) (end-cont)))

(define dec-var car)
(define dec-args cadr)
(define dec-body caddr)

(define (macro-translate exp1)
  (define (>> exp1) (macro-translate exp1))
  (match exp1
    ; a variable
    [(? symbol? s) s]
    ; a number
    [(? number? n) n]
    ; a boolean
    [(? boolean? b) b]
    ; a procedure
    [`(lambda ,a ,b) `(lambda ,a ,(>> b))]
    ; a letrec expression
    [`(letrec ,decs ,body)
     `(letrec ,(map (lambda (dec)
                      (list (dec-var dec) (dec-args dec) (>> (dec-body dec))))
                    decs)
        ,(>> body))]
    ; a begin expression
    [`(begin . ,exps) `(begin . ,(map >> exps))]
    ; a set expression
    [`(set! ,v ,e) `(set! ,v ,(>> e))]
    ; a letcc expression
    [`(letcc ,v ,e) `(letcc ,v ,(>> e))]
    ; a raise expression
    [`(raise ,e) `(raise ,(>> e))]
    ; a catch expression
    [`(catch ,body with ,var ,p-body)
     `(catch ,(>> body) with ,var ,(>> p-body))]
    ; a if expression
    [`(if ,e1 ,e2 ,e3)
     `((ifv ,(>> e1) (lambda () ,(>> e2)) (lambda () ,(>> e3))))]
    ; a let expression
    [`(let ,decs ,body)
     (let ((vars (map car decs))
           (exps (map cadr decs)))
       `((lambda ,vars ,(>> body)) . ,(map >> exps)))]
    ; a recursive procedure
    [`(fix ,f ,as ,b)
     `(letrec ((,f ,as ,(>> b))) ,f)]
    ; a cc epxression
    [`(cc ,e1 ,e2) `(,(>> e1) ,(>> e2))]
    ; an application
    [`(,ef . ,exps) `(,(>> ef) . ,(map >> exps))]))

(define (value-of/k exp1 env cont)
  (gc (void) env cont)
  (match exp1
    ; a variable
    [(? symbol? s) (apply-cont cont (deref (apply-env env s)))]
    ; a number
    [(? number? n) (apply-cont cont n)]
    ; a boolean
    [(? boolean? b) (apply-cont cont b)]
    ; a procedure
    [`(lambda ,args ,body) (apply-cont cont (closure args body env))]
    ; a letrec expression
    [`(letrec ,decs ,body)
     (let ((vars (map dec-var decs))
           (argss (map dec-args decs))
           (bodies (map dec-body decs)))
       (value-of/k body (extend-env-letrec env vars argss bodies) cont))]
    ; a begin expression
    [`(begin . ,exps)
     (if (null? exps)
         (apply-cont cont (void))
         (apply-cont (begin-cont cont env exps) (void)))]
    ; a set expression
    [`(set! ,v ,e)
     (value-of/k e env (set-cont cont env v))]
    ; a letcc expression
    [`(letcc ,v ,e)
     (value-of/k e (extend-env-let env (list v) (list (contval cont))) cont)]
    ; a raise expression
    [`(raise ,e)
     (value-of/k e env (raise-cont cont))]
    ; a catch expression
    [`(catch ,body with ,var ,p-body)
     (value-of/k body env (catch-cont cont env var p-body))]
    ; an application
    [`(,ef . ,exps)
     (value-of/k ef env (args-cont cont env exps))]))

; environment
(struct empty-env () #:transparent)
(struct extend-env (env vars refs) #:transparent)

(define (extend-env-let env vars vals)
  (let ((nvars (length vars))
        (nvals (length vals))
        (refs (map newref vals)))
    (if (= nvars nvals)
        (extend-env env vars refs)
        (report-num-args-not-match nvars nvals))))

(define (extend-env-letrec env vars argss bodies)
  ; assert (= nvars nargss nbodies)
  (define (allocn n)
    (if (= n 0)
        '()
        (cons (newref 'uninitialized) (allocn (- n 1)))))
  (let* ((refs (allocn (length vars)))
         (new-env (extend-env env vars refs)))
    (for-each setref!
              refs
              (map (lambda (args body) (closure args body new-env))
                   argss bodies))
    new-env))

(define (apply-env-f env search-var f)
  (cond
   [(empty-env? env) (f)]
   [(extend-env? env)
    (define (iter vars refs)
      (if (null? vars)
          (apply-env-f (extend-env-env env) search-var f)
          (if (eqv? search-var (car vars))
              (car refs)
              (iter (cdr vars) (cdr refs)))))
    (iter (extend-env-vars env) (extend-env-refs env))]))

(define (apply-env env search-var)
  (apply-env-f env
               search-var
               (lambda () (report-unbound-var search-var))))

; store
(define the-store 'uninitialized)
(define the-store-offset 'uninitialized)
(define the-store-free-list 'uninitialized)
(struct reference (n) #:transparent)

(define (initialize-store! size)
  (set! the-store (make-vector size))
  (set! the-store-offset 0)
  (set! the-store-free-list '()))

(define (newref val)
  (reference
   (if (null? the-store-free-list)
       (if (< the-store-offset the-max-store-size)
           (begin
             (vector-set! the-store the-store-offset val)
             (let ((off the-store-offset))
               (set! the-store-offset (+ the-store-offset 1))
               off))
           (report-out-of-memory))
       (let ((off (car the-store-free-list)))
         (vector-set! the-store off val)
         (set! the-store-free-list (cdr the-store-free-list))
         off))))

(define (deref ref)
  (vector-ref the-store (reference-n ref)))

(define (setref! ref val)
  (vector-set! the-store (reference-n ref) val))

(define (store-info)
  (let* ((start (length opd-table))
         (size (- the-store-offset start))
         (vec (make-vector size)))
    (define (iter i)
      (if (< i size)
          (begin
            (vector-set! vec i (vector-ref the-store (+ start i)))
            (iter (+ i 1)))
          (void)))
    (iter 0)
    (cons start vec)))

; continuation
(define (print-info info)
  (displayln info)
  (display "Store: ")
  (pretty-print (store-info)))

(define (end-cont)
  (lambda (msg)
    (match msg
      ('end? #t)
      ('catch? #f)
      ('get-vals '())
      ('apply (lambda (v) (print-info ">> Done!") v)))))

(define (cont-with-env cont env app-func)
  (lambda (msg)
    (match msg
      ('end? #f)
      ('catch? #f)
      ('get-vals '())
      ('get-prev cont)
      ('get-env env)
      ('apply app-func))))

(define (begin-cont cont env exps)
  ; assert (not (null? exps))
  (cont-with-env
   cont
   env
   (lambda (_)
     (let ((rest (cdr exps)))
       (if (null? rest)
           (value-of/k (car exps) env cont)
           (value-of/k (car exps)
                       env
                       (begin-cont cont env rest)))))))

(define (set-cont cont env var)
  (cont-with-env
   cont
   env
   (lambda (v)
     (setref! (apply-env env var) v)
     (apply-cont cont (void)))))

(define (args-cont cont env exps)
  (cont-with-env
   cont
   env
   (lambda (v)
     (if (null? exps)
         (apply-proc/k v '() cont)
         (value-of/k (car exps)
                     env
                     (fun-cont cont env v '() (cdr exps)))))))

(define (fun-cont cont env rator vals exps)
  (lambda (msg)
    (match msg
      ['get-vals (cons rator vals)]
      [else
       ((cont-with-env
         cont
         env
         (lambda (v)
           (let ((new-vals (append vals (list v))))
             (if (null? exps)
                 (apply-proc/k rator new-vals cont)
                 (value-of/k (car exps)
                             env
                             (fun-cont cont env rator new-vals (cdr exps)))))))
        msg)])))

(define (raise-cont cont)
  (cont-with-env
   cont
   (empty-env)
   (lambda (v)
     (cond
      [(end-cont? cont) (print-info ">> Exception!") v]
      [(catch-cont? cont) (catch-raise-cont cont v)]
      [else (apply-cont (raise-cont (cont-prev cont)) v)]))))

(define (catch-cont cont env var p-body)
  (lambda (msg)
    (match msg
      ['catch
       (lambda (v)
         (value-of/k p-body (extend-env-let env (list var) (list v)) cont))]
      ['catch? #t]
      [else
       ((cont-with-env cont (empty-env) (lambda (v) (apply-cont cont v)))
        msg)])))

(define (end-cont? cont) (cont 'end?))

(define (catch-cont? cont) (cont 'catch?))
(define (catch-raise-cont cont v) ((cont 'catch) v))

(define (cont-prev cont) (cont 'get-prev))
(define (cont-env cont) (cont 'get-env))
(define (cont-vals cont) (cont 'get-vals))

(define (apply-cont cont v)
  (gc v (empty-env) cont)
  ((cont 'apply) v))

; closure
(struct closure (args body env))

(define (apply-closure/k clo vals cont)
 (let ((args (closure-args clo))
       (body (closure-body clo))
       (env (closure-env clo)))
   (value-of/k body (extend-env-let env args vals) cont)))

; opd
(struct operation (name opd) #:transparent)
(struct mutpair (left-ref right-ref) #:transparent)

(define (-ifv b v1 v2) (if (true? b) v1 v2))

(define (-pair vl vr) (mutpair (newref vl) (newref vr)))
(define (-left pair) (deref (mutpair-left-ref pair)))
(define (-right pair) (deref (mutpair-right-ref pair)))

(define (-setleft! pair val)
  (setref! (mutpair-left-ref pair) val)
  (void))
(define (-setright! pair val)
  (setref! (mutpair-right-ref pair) val)
  (void))

(define (-print val) (displayln val))

(define (true? x) (eqv? x #t))
(define (false? x) (eqv? x #f))

(define opd-table
  (map (lambda (p)
         (cons (car p) (operation (car p) (cdr p))))
       (list
        (cons 'ifv -ifv)
        (cons '+ +)
        (cons '* *)
        (cons '- -)
        (cons 'remainder remainder)
        (cons 'zero? zero?)
        (cons 'pair -pair)
        (cons 'mutpair? mutpair?)
        (cons 'left -left)
        (cons 'right -right)
        (cons 'setleft! -setleft!)
        (cons 'setright! -setright!)
        (cons 'print -print))))

(define (init-env)
  (extend-env-let (empty-env) (map car opd-table) (map cdr opd-table)))

(define (apply-opd/k opd vals cont)
  (apply-cont cont (apply (operation-opd opd) vals)))

; apply-proc
(struct contval (val))  ; continuation value

(define (apply-proc/k proc vals cont)
  (cond
   [(closure? proc) (apply-closure/k proc vals cont)]
   [(operation? proc) (apply-opd/k proc vals cont)]
   [(contval? proc)
    (if (= 1 (length vals))
        (apply-cont (contval-val proc) (car vals))
        (report-apply-continuation-not-match vals))]
   [else (report-not-a-proc proc)]))

; gc
(define (gc val env cont)
  (define flags (make-vector the-store-offset 'white))
  (define grays '())
  (define (mark-ref ref)
    (let ((i (reference-n ref)))
      (if (eqv? (vector-ref flags i) 'white)
          (begin
            (vector-set! flags i 'gray)
            (set! grays (cons i grays)))
          (void))))
  (define (mark-env env)
    (if (empty-env? env)
        (void)
        (let ((refs (extend-env-refs env))
              (closing-env (extend-env-env env)))
          (for-each mark-ref refs)
          (mark-env closing-env))))
  (define (mark-cont cont)
    (if (end-cont? cont)
        (void)
        (begin
          (for-each mark-val (cont-vals cont))
          (mark-env (cont-env cont))
          (mark-cont (cont-prev cont)))))
  (define (set-free-list!)
    (define (whites acc i)
      (if (< i 0)
          acc
          (if (eqv? (vector-ref flags i) 'white)
              (whites (cons i acc) (- i 1))
              (whites acc (- i 1)))))
    (set! the-store-free-list (whites '() (- the-store-offset 1))))
  (define (mark-val v)
    (cond
     [(closure? v)
      (mark-env (closure-env v))]
     [(mutpair? v)
      (mark-ref (mutpair-left-ref v))
      (mark-ref (mutpair-right-ref v))]
     [(contval? v)
      (mark-cont (contval-val v))]))
  (define (iter)
    (if (null? grays)
        (void)
        (begin
          (let* ((i (car grays))
                 (v (vector-ref the-store i)))
            (set! grays (cdr grays))
            (vector-set! flags i 'black)
            ;(printf "~a: ~a~%" i v)
            (mark-val v))
          (iter))))
  (begin
    (mark-val val)
    (mark-env env)
    (mark-cont cont)
    (iter)
    (set-free-list!)))

; report error
(define (report-unbound-var var)
  (error "[Error] unbound var:" var))

(define (report-not-a-proc proc)
  (error "[Error] not a procedure:" proc))

(define (report-num-args-not-match nvars nvals)
  (error "[Error] num args not match (nvars nvals):" nvars nvals))

(define (report-out-of-memory)
  (error "[Error] running out of memory:" (store-info)))

(define (report-apply-continuation-not-match vals)
  (error "[Error] continuation expects 1 argument but got" (length vals) vals))

; test
(require "test-cases.rkt")
(test interp alligator-cases)
