#lang racket

; Expression = Variable
;            | Number
;            | Boolean
;            | (lambda (Variable*) Expression)
;            | (letrec ((Variable (Variable*) Expression)*) Expression)
;            | (if Expression Expression Expression)
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
;  void: () -> <void>
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
;
;===cps=================================================
;
; SiExp = Variable
;       | Number
;       | Boolean
;       | (lambda (Variable*) TfExp)
;
; TfExp = SiExp
;       | (letrec ((Variable (Variable*) TfExp)*) TfExp)
;       | (if SiExp TfExp TfExp)
;       | (set! Variable SiExp SiExp) ; (set! var val cont)
;       | (app SiExp SiExp* SiExp SiExp) ; (app fun args* cont econt)
;
; Cont = ECont = Variable | (lambda (Variable) TfExp)
;
; Value = Number
;       | Boolean
;       | Closure
;       | Opd/k
;       | <void>
;       | Mutpair
;
; (opd/k args... cont econt) = (cont (opd args...))

(define the-max-store-size 96)
(define (interp exp1)
  (reset-space-cost!)
  (initialize-store! the-max-store-size)
  (init-newvar!)
  (let* ((cps-exp (cps-translate (opd-translate
                                  (macro-translate exp1))
                                 '(lambda (v) v)
                                 '(lambda (e) e)))
         (opd-exp (optimize cps-exp)))
    (displayln "CPS:")
    (pretty-print cps-exp)
    (if (not (cmp-exp cps-exp opd-exp))
        (begin
          (displayln "optimized:")
          (pretty-print opd-exp))
        (void))
    (let ((ret (value-of opd-exp (init-env))))
      ;(displayln (store-info))
      (printf "#SpaceCost=~a~%" the-space-cost)
      ret)) )

(define (cmp-exp e1 e2)
  (if (and (pair? e1) (pair? e2))
      (and (cmp-exp (car e1) (car e2))
           (cmp-exp (cdr e1) (cdr e2)))
      (eqv? e1 e2)))

(define (constant? x)
  (or (number? x) (boolean? x)))

(define the-space-cost 0)
(define (reset-space-cost!)
  (set! the-space-cost 0))
(define (update-space-cost!)
  (let ((cost (- the-store-offset
                 the-num-opds
                 (length the-store-free-list))))
    (set! the-space-cost (max the-space-cost cost))))

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
    [`(lambda ,as ,b) `(lambda ,as ,(>> b))]
    ; a letrec expression
    [`(letrec ,decs ,body)
     `(letrec ,(map (lambda (dec)
                      `(,(dec-var dec) ,(dec-args dec) ,(>> (dec-body dec))))
                    decs)
        ,(>> body))]
    ; a if expression
    [`(if ,e1 ,e2 ,e3) `(if ,(>> e1) ,(>> e2) ,(>> e3))]
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

; tmp variable
(define the-newvar-count 'uninitialized)
(define (init-newvar!) (set! the-newvar-count 0))
(define (newvar)
  (set! the-newvar-count (+ the-newvar-count 1))
  (string->symbol
       (string-append "#" (number->string the-newvar-count))))

; a variable stands for continuation
(define (mkvar s)
  (string->symbol (string-append "#" (symbol->string s))))
(define vark (mkvar 'k))
(define varek (mkvar 'ek))

; a variable stands for useless arguement
(define var_ (mkvar '_))

(define (pushback lst . vs) (append lst vs))

(define (list-last lst)
  ; assert (not (null? lst))
  (if (null? (cdr lst)) (car lst) (list-last (cdr lst))))

(define (partition-last2-f lst f)
  ; assert (>= (length lst) 2)
  (define (iter racc lst)
    (if (null? (cddr lst))
        (f (car lst) (cadr lst) (reverse racc))
        (iter (cons (car lst) racc) (cdr lst))))
  (iter '() lst))

(define (list-in? elem lst)
  (cond
   [(null? lst) #f]
   [(eqv? elem (car lst)) #t]
   [else (list-in? elem (cdr lst))]))

(define (apply-list procs v)
  (foldl (lambda (f v) (f v)) v procs))

(define (simple-exp? exp1)
  (match exp1
    [(? symbol? s) #t]
    [(? number? n) #t]
    [(? boolean? b) #t]
    [`(lambda ,as ,b) #t]
    [else #f]))

(define (opd-translate exp1)
  (define (opd-translate/c exp1 covered-opds)
    (define (append-opds ss)
      (append (filter in-opd-table ss) covered-opds))
    (define (>>/c e ss) (opd-translate/c e (append-opds ss)))
    (define (>> e) (opd-translate/c e covered-opds))
    (match exp1
      [(? symbol? s)
       (if (and (in-opd-table s)
                (not (list-in? s covered-opds)))
           (mkvar s)
           s)]
      [(? number? n) n]
      [(? boolean? b) b]
      [`(lambda ,as ,b)
       `(lambda ,as ,(>>/c b as))]
      [`(letrec ,decs ,body)
       `(letrec
            ,(map (lambda (dec)
                    `(,(dec-var dec)
                      ,(dec-args dec)
                      ,(>>/c (dec-body dec) (dec-args dec))))
                  decs)
          ,(>>/c body (map dec-var decs)))]
      [`(if ,e1 ,e2 ,e3) `(if ,(>> e1) ,(>> e2) ,(>> e3))]
      [`(begin . ,exps)
       `(begin . ,(map >> exps))]
      [`(set! ,v ,e) `(set! ,v ,(>> e))]
      [`(letcc ,v ,e) `(letcc ,v ,(>> e))]
      [`(raise ,e) `(raise ,(>> e))]
      [`(catch ,body with ,var ,p-body)
       `(catch ,(>> body) with ,var ,(>>/c p-body (list var)))]
      [(? list? exps) (map >> exps)]))
  (opd-translate/c exp1 '()))

(define (cps-translate exp1 cont econt)
  (define (>> e) (cps-translate e cont econt))
  (define (>>/k e k ek) (cps-translate e k ek))
  (define (>>s sexp)
    (match sexp
      ; a variable
      [(? symbol? s) s]
      ; a number
      [(? number? n) n]
      ; a boolean
      [(? boolean? b) b]
      ; a procedure
      [`(lambda ,as ,b)
       `(lambda ,(pushback as vark varek) ,(>>/k b vark varek))]))
  (define (>>lst acc exps put get)
    (if (null? exps)
        (get acc)
        (let ((e (car exps)))
          (if (simple-exp? e)
              (>>lst (put acc e) (cdr exps) put get)
              (let ((w (newvar)))
                (>>/k e
                      `(lambda (,w)
                         ,(>>lst (put acc w) (cdr exps) put get))
                      econt))))))
  (match exp1
    ; a SiExp
    [(? simple-exp? sexp) `(app ,cont ,(>>s sexp))]
    ; a letrec expression
    [`(letrec ,decs ,body)
     `(letrec ,(map (lambda (dec)
                      (list (dec-var dec)
                            (pushback (dec-args dec) vark varek)
                            (>>/k (dec-body dec) vark varek)))
                    decs)
        ,(>> body))]
    ; an if expression
    [`(if ,e1 ,e2 ,e3)
     (if (simple-exp? e1)
         `(if ,(>>s e1) ,(>> e2) ,(>> e3))
         (let ((w (newvar)))
           (>>/k e1 `(lambda (,w) (if ,w ,(>> e2) ,(>> e3))) econt)))]
    ; a begin expression (the begin expression disappears)
    [`(begin . ,exps)
     (if (null? exps)
         (>> `(,(mkvar 'void)))
         (let* ((rexps (reverse exps))
                (last (car rexps))
                (heads (reverse (cdr rexps))))
           (>>lst 'not-used-value
                   heads
                   (lambda (acc v) v)
                   (lambda (acc) (>> last)))))]
    ; a set expression
    [`(set! ,v ,e)
     (if (simple-exp? e)
         `(set! ,v ,(>>s e) ,cont)
         (let ((w (newvar)))
           (>>/k e `(lambda (,w) (set! ,v ,w ,cont)) econt)))]
    ; a letcc expression (the letcc expression disappears)
    [`(letcc ,v ,e)
     (let ((w (newvar)))
       `(app (lambda (,v) ,(>> e)) (lambda (,w ,var_ ,var_) (app ,cont ,w))))]
    ; a raise expression
    [`(raise ,e)
     (if (simple-exp? e)
         `(app ,econt ,(>>s e))
         (let ((w (newvar)))
           (>>/k e `(lambda (,w) (app ,econt ,w)) econt)))]
    ; a catch expression (the catch expression disappears)
    [`(catch ,body with ,var ,p-body)
     (>>/k body cont `(lambda (,var) ,(>> p-body)))]
    ; an application
    [`(,ef . ,exps)
     (>>lst '()
            exp1
            (lambda (racc v) (cons v racc))
            (lambda (racc)
              `(app . ,(pushback (map >>s (reverse racc)) cont econt))))]))

; optimize
(define (optimize cps-exp)
  (define (mark-wrap f)
    (lambda (e) (unmark-variable
                 (f
                  (mark-variable e)))))
  (define (iter cps-exp)
    (let ((opd-exp (apply-list (list (mark-wrap beta-reduction)
                                     (mark-wrap eta-reduction)
                                     constant-folding)
                               cps-exp)))
      (if (cmp-exp opd-exp cps-exp)
          opd-exp
          (iter opd-exp))))
  ;(displayln "mark:")
  ;(pretty-print (mark-variable cps-exp))
  (iter cps-exp))

(define (mark-variable cps-exp)
  (define (>>/e cps-exp menv)
    (define (>> e) (>>/e e menv))
    (define (make-scp as)
      ; entry: (name . #(count dirty?))
      (map (lambda (a) (cons a (vector 0 #t))) as))
    (define (try-scp-f f)
      (lambda (scp s)
        (let ((entry (assoc s scp)))
          (if entry
              (begin
                (f (cdr entry))
                #t)
              #f))))
    (define (do-menv-f menv s f)
      (cond
       [(null? menv) s]
       [(f (car menv) s) s]
       [else (do-menv-f (cdr menv) s f)]))
    (define (add-menv menv s)
      (do-menv-f
       menv
       s
       (try-scp-f (lambda (vec)
                    (vector-set! vec 0 (+ 1 (vector-ref vec 0)))))))
    (define (mark-menv menv s)
      (do-menv-f
       menv
       s
       (try-scp-f (lambda (vec)
                    (vector-set! vec 0 (+ 1 (vector-ref vec 0)))
                    (vector-set! vec 1 #f)))))
    (match cps-exp
      [(? symbol? s) (add-menv menv s)]
      [(? number? n) n]
      [(? boolean? b) b]
      [`(lambda ,as ,b)
       (let* ((scp (make-scp as))
              (new-body (>>/e b (cons scp menv)))
              (new-as (map (lambda (ent)
                             (cons (car ent) (vector->list (cdr ent))))
                           scp)))
         `(lambda ,new-as ,new-body))]
      [`(letrec ,decs ,body)
       (let ((new-menv (cons (make-scp (map dec-var decs)) menv)))
         `(letrec ,(map (lambda (dec)
                          `(,(dec-var dec)
                            ,(dec-args dec)
                            ,(>>/e (dec-body dec)
                                   (cons (make-scp (dec-args dec)) new-menv))))
                        decs)
            ,(>>/e body new-menv)))]
      [`(if ,se ,e2 ,e3) `(if ,(>> se) ,(>> e2) ,(>> e3))]
      [`(set! ,var ,se ,cont)
       (begin
         (mark-menv menv var)
         `(set! ,var ,(>> se) ,(>> cont)))]
      [`(app . ,exps) `(app . ,(map >> exps))]))
  (>>/e cps-exp '()))

(define (unmark-variable cps-exp)
  (define >> unmark-variable)
  (match cps-exp
    [(? symbol? s) s]
    [(? number? n) n]
    [(? boolean? b) b]
    [`(lambda ,as ,b) `(lambda ,(map car as) ,(>> b))]
    [`(letrec ,decs ,body)
     `(letrec ,(map (lambda (dec)
                      `(,(dec-var dec) ,(dec-args dec) ,(>> (dec-body dec))))
                    decs)
        ,(>> body))]
    [`(if ,se ,e2 ,e3) `(if ,(>> se) ,(>> e2) ,(>> e3))]
    [`(set! ,var ,se ,cont) `(set! ,var ,(>> se) ,(>> cont))]
    [`(app . ,exps) `(app . ,(map >> exps))]))

(define (pass cps-exp >>)
  (match cps-exp
    [(? symbol? s) s]
    [(? number? n) n]
    [(? boolean? b) b]
    [`(lambda ,as ,b) `(lambda ,as ,(>> b))]
    [`(letrec ,decs ,body)
     `(letrec ,(map (lambda (dec)
                      `(,(dec-var dec) ,(dec-args dec) ,(>> (dec-body dec))))
                    decs)
        ,(>> body))]
    [`(if ,se ,e2 ,e3) `(if ,(>> se) ,(>> e2) ,(>> e3))]
    [`(set! ,var ,se ,cont) `(set! ,var ,(>> se) ,(>> cont))]
    [`(app . ,exps) `(app . ,(map >> exps))]))

(define (beta-reduction cps-exp)
  (define (extend-env-all env vars vals)
    (append (map cons vars vals) env))
  (define (extend-env env var val)
    (cons (cons var val) env))
  (define (apply-env env var)
    (let ((p (assoc var env))) (if p (cdr p) var)))
  (define (>>/e cps-exp env)
    (define (>> e) (>>/e e env))
    (match cps-exp
      [(? symbol? s) (apply-env env s)]
      [`(set! ,var ,se ,cont) `(set! ,(>> var) ,(>> se) ,(>> cont))]
      [`(app (lambda ,args ,body) . ,vals)
       (define (sub? a v) (and (caddr a)
                               (or (= 1 (cadr a))
                                   (constant? v)
                                   (symbol? v))))
       (define (sub-lst? as vs)
         ; assert (= (length as) (length vs))
         (cond
          [(null? as) #f]
          [(sub? (car as) (car vs)) #t]
          [else (sub-lst? (cdr as) (cdr vs))]))
       (define (iter new-as new-vs as vs new-env)
         ; assert (= (length as) (length vs))
         (if (null? as)
             (if (null? new-as)
                 (>>/e body new-env)
                 `(app (lambda ,new-as ,(>>/e body new-env)) . ,new-vs))
             (let ((a (car as))
                   (v (car vs))
                   (as (cdr as))
                   (vs (cdr vs)))
               (cond
                [(= 0 (cadr a)) (iter new-as new-vs as vs new-env)]
                [(sub? a v)
                 (iter new-as new-vs as vs (extend-env new-env (car a) (>> v)))]
                [else (let ((new-a (cons (newvar) (cdr a))))
                        (iter (pushback new-as new-a)
                              (pushback new-vs (>> v))
                              as
                              vs
                              (extend-env new-env (car a) (car new-a))))]))))
       (let ((nvars (length args))
             (nvals (length vals)))
         (if (= nvars nvals)
             (if (sub-lst? args vals)
                 (iter '() '() args vals env)
                 `(app (lambda ,args ,(>> body)) . ,(map >> vals)))
             (report-num-args-not-match nvars nvals)))]
      [`(lambda ,as ,b)
       (if (null? env)
           `(lambda ,as ,(>> b))
           (let ((new-as (map (lambda (a) (cons (newvar) (cdr a))) as)))
             `(lambda ,new-as
                ,(>>/e b (extend-env-all env
                                         (map car as)
                                         (map car new-as))))))]
      [`(letrec ,decs ,body)
       (if (null? env)
           `(letrec ,(map (lambda (dec)
                            `(,(dec-var dec)
                              ,(dec-args dec)
                              ,(>> (dec-body dec))))
                          decs)
              ,(>> body))
           (let* ((fs (map dec-var decs))
                  (new-fs (map (lambda (a) (newvar)) fs))
                  (new-env (extend-env-all env fs new-fs)))
             `(letrec ,(map (lambda (new-f&dec)
                              (let* ((new-f (car new-f&dec))
                                     (dec (cdr new-f&dec))
                                     (as (dec-args dec))
                                     (new-as (map (lambda (a) (newvar)) as)))
                                `(,new-f
                                  ,new-as
                                  ,(>>/e (dec-body dec)
                                         (extend-env-all new-env as new-as)))))
                            (map cons new-fs decs))
                ,(>>/e body new-env))))]
      [else (pass cps-exp >>)]))
  (>>/e cps-exp '()))

(define (eta-reduction cps-exp)
  (define >> eta-reduction)
  (define (check-args? args vals)
    (cond
     [(null? args) (null? vals)]
     [(null? vals) #f]
     [(and (= 1 (cadar args))
           (eqv? (caar args) (car vals)))
      (check-args? (cdr args) (cdr vals))]
     [else #f]))
  (match cps-exp
    [`(lambda ,args (app ,f . ,vals))
     (if (check-args? args vals)
         (>> f)
         `(lambda ,args (app ,(>> f) . ,(map >> vals))))]
    [else (pass cps-exp >>)]))

(define (constant-folding cps-exp)
  (define opd+ (mkvar '+))
  (define opd* (mkvar '*))
  (define opd- (mkvar '-))
  (define opdremainder (mkvar 'remainder))
  (define opdzero? (mkvar 'zero?))
  (define (eqv-to? v) (lambda (x) (eqv? x v)))
  (define >> constant-folding)
  (define (pick-num&cont-f exps opd f)
    (partition-last2-f
     exps
     (lambda (cont econt vals)
       (define (iter nums rest vals)
         (cond
          [(null? vals)
           (f (>> cont)
              (>> econt)
              (apply opd (reverse nums))
              (map >> (reverse rest)))]
          [(number? (car vals))
           (iter (cons (car vals) nums) rest (cdr vals))]
          [else
           (iter nums (cons (car vals) rest) (cdr vals))]))
       (iter '() '() vals))))
  (match cps-exp
    [`(if ,se ,e2 ,e3)
     (if (boolean? se)
         (if se (>> e2) (>> e3))
         `(if ,(>> se) ,(>> e2) ,(>> e3)))]
    [(cons app (cons (? (eqv-to? opd+)) exps))
     (pick-num&cont-f
      exps
      +
      (lambda (cont econt ret rest)
        (cond
         [(null? rest) `(app ,cont ,ret)]
         [(= 0 ret)
          `(app ,opd+ . ,(pushback rest cont econt))]
         [else
          `(app ,opd+ . ,(pushback rest ret cont econt))])))]
    [(cons app (cons (? (eqv-to? opd*)) exps))
     (pick-num&cont-f
      exps
      *
      (lambda (cont econt ret rest)
        (cond
         [(null? rest) `(app ,cont ,ret)]
         [(= 1 ret)
          `(app ,opd* . ,(pushback rest cont econt))]
         [else
          `(app ,opd* . ,(pushback rest ret cont econt))])))]
    [(cons app (cons (? (eqv-to? opd-)) `(,e1 . ,exps)))
     (pick-num&cont-f
      exps
      +
      (lambda (cont econt ret rest)
        (cond
         [(not (number? e1))
          (if (= 0 ret)
              `(app ,opd- ,e1 . ,(pushback rest cont econt))
              `(app ,opd- ,e1 . ,(pushback rest ret cont econt)))]
         [(null? rest) `(app ,cont ,(- e1 ret))]
         [else
          `(app ,opd- ,(- e1 ret) . ,(pushback rest cont econt))])))]
    [(cons app (cons (? (eqv-to? opdremainder)) exps))
     (let ((v1 (car exps))
           (v2 (cadr exps))
           (cont (caddr exps))
           (econt (cadddr exps)))
       (if (and (number? v1) (number? v2))
           `(app ,(>> cont) ,(remainder v1 v2))
           `(app ,opdremainder . ,(map >> exps))))]
    [(cons app (cons (? (eqv-to? opdzero?)) exps))
     (let ((v (car exps))
           (cont (cadr exps))
           (econt (caddr exps)))
       (if (number? v)
           `(app ,(>> cont) ,(zero? v))
           `(app ,opdzero? . ,(map >> exps))))]
    [else (pass cps-exp >>)]))

; value-of
(define (value-of cps-exp env)
  (define (>> sexp)
    (match sexp
      ; a variable
      [(? symbol? s) (deref (apply-env env s))]
      ; a number
      [(? number? n) n]
      ; a boolean
      [(? boolean? b) b]
      ; a procedure
      [`(lambda ,as ,b) (closure as b env)]))
  ; gc
  (update-space-cost!)
  (gc env)
  ; eval
  (match cps-exp
    ; SiExp
    [(? simple-exp? sexp) (>> sexp)]
    ; letrec
    [`(letrec ,decs ,body)
     (let ((vars (map dec-var decs))
           (argss (map dec-args decs))
           (bodies (map dec-body decs)))
       (value-of body (extend-env-letrec env vars argss bodies)))]
    ; if
    [`(if ,se ,e2 ,e3)
     (let ((val (>> se)))
       (cond
        [(true? val) (value-of e2 env)]
        [(false? val) (value-of e3 env)]
        [else (report-if-condition-not-boolean val)]))]
    ; set!
    [`(set! ,var ,se ,cont)
     (setref! (apply-env env var) (>> se))
     (apply-closure (>> cont) (list (void)))]
    ; application
    (`(app ,sef . ,ses)
     (apply-proc (>> sef) (map >> ses)))))

; apply-proc
(define (apply-proc proc vals)
  (cond
   [(closure? proc) (apply-closure proc vals)]
   [(operation? proc) (apply-opd proc vals)]
   [else (report-not-a-proc proc)]))

; closure
(struct closure (args body env))
(define (apply-closure clo vals)
  (value-of (closure-body clo)
            (extend-env-let (closure-env clo)
                            (closure-args clo)
                            vals)))

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
  (let ((i (reference-n ref)))
    (if (< i the-num-opds)
        (report-immutable-variable (operation-name (deref ref)))
        (vector-set! the-store i val))))

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
        (cons 'void void)
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
(define the-num-opds (length opd-table))

(define (in-opd-table s) (assoc s opd-table))

(define (init-env)
  (extend-env-let (empty-env)
                  (map (lambda (o) (mkvar (car o))) opd-table)
                  (map cdr opd-table)))

(define (apply-opd opd vals)
  (partition-last2-f vals
                     (lambda (cont econt vals)
                       (apply-closure cont
                                      (list (apply (operation-opd opd) vals))))))

; gc
(define (gc env)
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
      (mark-ref (mutpair-right-ref v))]))
  (define (iter)
    (if (null? grays)
        (void)
        (begin
          (let* ((i (car grays))
                 (v (vector-ref the-store i)))
            (set! grays (cdr grays))
            (vector-set! flags i 'black)
            (mark-val v))
          (iter))))
  (begin
    (mark-env env)
    (iter)
    (set-free-list!)))

; report error
(define (report-unbound-var var)
  (error "[Error] unbound var:" var))

(define (report-if-condition-not-boolean val)
  (error "[Error] if condition not boolean:" val))

(define (report-not-a-proc proc)
  (error "[Error] not a procedure:" proc))

(define (report-num-args-not-match nvars nvals)
  (error "[Error] num args not match (nvars nvals):" nvars nvals))

(define (report-out-of-memory)
  (error "[Error] running out of memory:" (store-info)))

(define (report-immutable-variable var)
  (error "[Error] immutable variable:" var))

; test
(require "test-cases.rkt")
(test interp alligator-cases)
