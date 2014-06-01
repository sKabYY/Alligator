#lang racket

; Expression = Variable
;            | Number
;            | Boolean
;            | (lambda (Variable*) Expression)
;            | (if Expression Expression Expression)
;            | (let ((Variable Expression)*) Expression)
;            | (letrec ((Variable (Variable*) Expression)*) Expression)
;            | (begin Expression*)
;            | (set! Variable Expression)
;            | (Expression Expression*)
;
; Type = SimpleType | UnionType
; TypeOrVar = Type | Variable
; SimpleType =
;            | Any
;            | Num
;            | Bool
;            | (-> Type Type)  ; procedure type
;            | Opd
;            | Void
;            | (* Type Type) ; pair
; UnionType: a set of SimpleType
;
; Value = Number
;       | Boolean
;       | Closure
;       | Opd
;       | <void>
;       | Mutpair
;
; Closure: (Variable*) * Expression * Environment
; Mutpair: Reference * Reference
;
; Opd:
;  +: Number * Number * ... -> Number
;  -: Number * Number * ...-> Number
;  *: Number * Number * ...-> Number
;  void: -> <void>
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
; Environment: Variable -> Reference
; Store: Reference -> Value

(provide interp)
(define the-max-store-size 32)
(define (interp exp1)
  (initialize-store! the-max-store-size)
  (reset-space-cost!)
  (value-of/k exp1 (init-env) (end-cont)))

(define (dec-var dec) (car dec))
(define (dec-exp dec) (cadr dec))
(define (rec-dec-var dec) (car dec))
(define (rec-dec-args dec) (cadr dec))
(define (rec-dec-body dec) (caddr dec))

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
    ; an if expression
    [`(if ,e1 ,e2 ,e3)
     (value-of/k e1 env (if-cont cont env e2 e3))]
    ; a let expression
    [`(let ,decs ,body)
     (value-of/k `((lambda ,(map dec-var decs) ,body)
                   ,@(map dec-exp decs))
                 env
                 cont)]
    ; a letrec expression
    [`(letrec ,rec-decs ,body)
     (let ((vars (map rec-dec-var rec-decs))
           (argss (map rec-dec-args rec-decs))
           (bodies (map rec-dec-body rec-decs)))
       (value-of/k body (extend-env-letrec env vars argss bodies) cont))]
    ; a begin expression
    [`(begin . ,exps)
     (cond
      [(null? exps) (apply-cont cont (void))]
      [(null? (cdr exps)) (value-of/k (car exps) env cont)]
      [else (value-of/k (car exps) env (begin-cont cont env (cdr exps)))])]
    ; a set expression
    [`(set! ,v ,e)
     (value-of/k e env (set-cont cont env v))]
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

(define the-space-cost 0)
(define (reset-space-cost!)
  (set! the-space-cost 0))
(define (update-space-cost!)
  (let ((cost (- the-store-offset
                 the-num-opds
                 (length the-store-free-list))))
    (set! the-space-cost (max the-space-cost cost))))

(define (store-info)
  (let* ((start the-num-opds)
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
  (printf "#SpaceCost=~a~%" the-space-cost))

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

(define (if-cont cont env then-exp else-exp)
  (cont-with-env
   cont
   env
   (lambda (v)
     (if v
         (value-of/k then-exp env cont)
         (value-of/k else-exp env cont)))))

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
        (cons '+ +)
        (cons '* *)
        (cons '- -)
        (cons 'void void)
        (cons 'remainder remainder)
        (cons 'zero? zero?)
        (cons 'pair -pair)
        (cons 'mutpair? mutpair?)
        (cons 'left -left)
        (cons 'right -right)
        (cons 'setleft! -setleft!)
        (cons 'setright! -setright!)
        (cons 'print -print))))
(define the-num-opds (length opd-table))

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
  (update-space-cost!)
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
(test interp alligator-ti-cases)
