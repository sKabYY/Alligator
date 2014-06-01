#lang racket

(provide (all-defined-out))

(define color-on #f)
(define (color code) (if color-on (display code) (void)))
(define (begin-red) (color "\033[91m"))
(define (begin-green) (color "\033[92m"))
(define (begin-yellow) (color "\033[93m"))
(define (end-color) (color "\033[0m"))

(define (test interp cases)
  (define (iter cases total wrong)
    (if (null? cases)
        (printf "SUMMARY(wrong/total): ~a/~a.~%" wrong total)
        (let ((exp1 (car cases))
              (ans (cadr cases))
              (rest (cddr cases)))
          (begin-green)
          (pretty-print exp1)
          (begin-red)
          (let* ((ret (interp exp1))
                 (correct (eqv? ret ans)))
            (display ">> ")
            (pretty-print ret)
            (begin-yellow)
            (if correct
                (void)
                (printf "[WRONG!]ans=~a~%" ans))
            (end-color)
            (newline)
            (iter rest (+ total 1) (if correct wrong (+ wrong 1)))))))
  (iter cases 0 0))

(define alligator-cases
  ; expression answer
  `(

12 13 ; being wrong for test
(+ 12 13) 25
(- 32 23) 9

((lambda (x) (- x 1)) 22) 21
(((lambda (x) x) (lambda (y) y)) 11) 11

(zero? 0) #t
(zero? 1) #f
(if (zero? 0) 1 2) 1
(if (zero? 1) 1 2) 2

((lambda (f) ((f f) 3))
 (lambda (p)
   (lambda (n)
     (if (zero? n)
         0
         (+ 2 ((p p) (- n 1))))))) 6

(((lambda (f)
    ((lambda (x) (f (x x)))
     (lambda (x) (f (lambda (v) ((x x) v))))))
  (lambda (f)
    (lambda (n)
      (if (zero? n)
          0
          (+ 2 (f (- n 1)))))))
 4) 8

(((lambda (f)
    ((lambda (x) (f (x x)))
     (lambda (x) (f (lambda (v1 v2) ((x x) v1 v2))))))
  (lambda (f)
    (lambda (n acc)
      (if (zero? n)
          acc
          (f (- n 1) (+ acc 2))))))
 4 0) 8

(let ((a 1))
  (+ a 2)) 3

(let ((f (lambda (p)
           (lambda (n)
             (if (zero? n)
                 0
                 (+ 2 ((p p) (- n 1))))))))
  ((f f) 4)) 8

((fix f (n)
      (if (zero? n)
          0
          (+ 2 (f (- n 1)))))
 4) 8

(letrec ((f (n) (if (zero? n)
                     0
                     (+ 2 (f (- n 1))))))
  (f 4)) 8

(letrec ((f (n acc) (if (zero? n)
                        acc
                        (f (- n 1) (+ acc 2)))))
  (f 4 0)) 8

(letrec ((gcd (a b) (if (zero? a)
                        b
                        (gcd (remainder b a) a))))
  (gcd 144 12144)) 48

(letrec ((gcd (a b) (if (zero? a)
                        b
                        (gcd (remainder b a) a))))
  ((lambda (a b c) (gcd a b)) 144 12144 444)) 48

(((lambda (x) x) +) 12 23) 35

(begin) ,(void)
(begin 12) 12

(let ((a 1))
  (begin
    (set! a 2)
    a)) 2

(letrec ((f (n) (if (zero? n) 0 (f (- n 1)))))
  (f 100)) 0

(letrec ((f (n) (if (zero? n) 0 (begin (f (- n 1))))))
  (f 100)) 0

(letrec ((f (a n) (if (zero? n) a (begin (f (+ a n) (- n 1))))))
  (f 0 100)) 5050

(let ((a 0))
  (letrec ((sum! (n) (if (zero? n)
                         a
                         (begin
                           (set! a (+ a n))
                           (sum! (- n 1))))))
    (sum! 100))) 5050

(print 777) ,(void)

(let ((p (pair 11 22)))
  (let ((x (left p))
        (y (right p)))
    (begin
      (setleft! p y)
      (setright! p x)
      (- (left p) (right p))))) 11

(letrec ((f (x) (if (mutpair? x)
                    (+ (f (left x)) (f (right x)))
                    1)))
  (f (pair (pair 1 2)
           (pair 3 (pair 4 5))))) 5

(let ((x 7))
  (+
   (let ((a 2)
         (b 3)
         (c 4))
     (* a b c))
   (let ((a 1)
         (b 2)
         (c 3))
     (+ a b c))
   x)) 37 ; test gc

(+ 1 (letcc x (+ (lambda (y) y) (cc x 12)))) 13
(+ 1 (letcc x (+ (lambda (y) y) (x 12)))) 13

(let ((call/cc (lambda (f)
                 (letcc k (f (lambda (y) (cc k y))))))
      (f (lambda (return x)
           (if (zero? x) -999 (return x)))))
  (call/cc (lambda (return) (f return 0)))) -999

(let ((call/cc (lambda (f)
                 (letcc k (f (lambda (y) (cc k y))))))
      (f (lambda (return x)
           (if (zero? x) -999 (return x)))))
  (call/cc (lambda (return) (f return 111)))) 111

(raise 123) 123
(catch 11 with e e) 11
(catch (raise 22) with e e) 22

(let ((index (lambda (n lst)
               (letrec ((inner
                         (lst)
                         (if (zero? (left lst))
                             (raise 99)
                             (if (zero? (- n (left lst)))
                                 0
                                 (+ 1 (inner (right lst)))))))
                 (catch (inner lst) with e -1)))))
  (index 5 (pair 1 (pair 2 (pair 0 0))))) -1

(let ((index (lambda (n lst)
               (letrec ((inner
                         (lst)
                         (if (zero? (left lst))
                             (raise 99)
                             (if (zero? (- n (left lst)))
                                 0
                                 (+ 1 (inner (right lst)))))))
                 (catch (inner lst) with e -1)))))
  (index 2 (pair 1 (pair 2 (pair 0 0))))) 1

(letcc c (+ 11 (raise (cc c 1)))) 1

(catch
 (let ((a 1)) (+ (letcc k (+ 122 (raise k))) a))
 with k (let ((a 10)) (cc k a))) 11

((lambda (a b) (set! a b)) 10 12) ,(void)

(let ((+ (+ 101 10)))
  (begin (set! + 222) +)) 222

(let ((a 111))
  (+ a (let ((a 222))
         (begin
           (set! a 999)
           a)))) 1110

((lambda (a b)
   ((lambda (x y) (+ a x y)) a b))
 11
 22) 44

(catch
 (+ 11 (letcc resume (raise (pair 2 resume))))
 with p
 (let ((n (left p))
       (resume (right p)))
   (if (zero? (- n 2))
       (resume n)
       n))) 13

(catch
 (+ 11 (letcc resume (raise (pair 12 resume))))
 with p
 (let ((n (left p))
       (resume (right p)))
   (if (zero? (- n 2))
       (resume n)
       n))) 12

))

(define alligator-ti-cases
  ; expression answer
  `(

12 13 ; being wrong for test
(+ 12 13) 25
(- 32 23) 9

((lambda (x) (- x 1)) 22) 21
(((lambda (x) x) (lambda (y) y)) 11) 11

(zero? 0) #t
(zero? 1) #f
(if (zero? 0) 1 2) 1
(if (zero? 1) 1 2) 2

((lambda (f) ((f f) 3))
 (lambda (p)
   (lambda (n)
     (if (zero? n)
         0
         (+ 2 ((p p) (- n 1))))))) 6

(((lambda (f)
    ((lambda (x) (f (x x)))
     (lambda (x) (f (lambda (v) ((x x) v))))))
  (lambda (f)
    (lambda (n)
      (if (zero? n)
          0
          (+ 2 (f (- n 1)))))))
 4) 8

(((lambda (f)
    ((lambda (x) (f (x x)))
     (lambda (x) (f (lambda (v1 v2) ((x x) v1 v2))))))
  (lambda (f)
    (lambda (n acc)
      (if (zero? n)
          acc
          (f (- n 1) (+ acc 2))))))
 4 0) 8

(let ((a 1))
  (+ a 2)) 3

(let ((f (lambda (p)
           (lambda (n)
             (if (zero? n)
                 0
                 (+ 2 ((p p) (- n 1))))))))
  ((f f) 4)) 8

(letrec ((f (n) (if (zero? n)
                     0
                     (+ 2 (f (- n 1))))))
  (f 4)) 8

(letrec ((f (n acc) (if (zero? n)
                        acc
                        (f (- n 1) (+ acc 2)))))
  (f 4 0)) 8

(letrec ((gcd (a b) (if (zero? a)
                        b
                        (gcd (remainder b a) a))))
  (gcd 144 12144)) 48

(letrec ((gcd (a b) (if (zero? a)
                        b
                        (gcd (remainder b a) a))))
  ((lambda (a b c) (gcd a b)) 144 12144 444)) 48

(((lambda (x) x) +) 12 23) 35

(begin) ,(void)
(begin 12) 12

(let ((a 1))
  (begin
    (set! a 2)
    a)) 2

(letrec ((f (n) (if (zero? n) 0 (f (- n 1)))))
  (f 100)) 0

(letrec ((f (n) (if (zero? n) 0 (begin (f (- n 1))))))
  (f 100)) 0

(letrec ((f (a n) (if (zero? n) a (begin (f (+ a n) (- n 1))))))
  (f 0 100)) 5050

(let ((a 0))
  (letrec ((sum! (n) (if (zero? n)
                         a
                         (begin
                           (set! a (+ a n))
                           (sum! (- n 1))))))
    (sum! 100))) 5050

(print 777) ,(void)

(let ((p (pair 11 22)))
  (let ((x (left p))
        (y (right p)))
    (begin
      (setleft! p y)
      (setright! p x)
      (- (left p) (right p))))) 11

(letrec ((f (x) (if (mutpair? x)
                    (+ (f (left x)) (f (right x)))
                    1)))
  (f (pair (pair 1 2)
           (pair 3 (pair 4 5))))) 5

(let ((x 7))
  (+
   (let ((a 2)
         (b 3)
         (c 4))
     (* a b c))
   (let ((a 1)
         (b 2)
         (c 3))
     (+ a b c))
   x)) 37 ; test gc

((lambda (a b) (set! a b)) 10 12) ,(void)

(let ((+ (+ 101 10)))
  (begin (set! + 222) +)) 222

(let ((a 111))
  (+ a (let ((a 222))
         (begin
           (set! a 999)
           a)))) 1110

((lambda (a b)
   ((lambda (x y) (+ a x y)) a b))
 11
 22) 44

(void) ,(void)

))
