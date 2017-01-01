#lang racket

;;; generate variable name with idx --- Proto type, not very good design
(define fv
  (lambda (v)
    (let ([n 0])
      (lambda ()
        (set! n (+ n 1))
        (string->symbol (string-append (symbol->string v) (number->string n)))))))



;;; Scheme Subset 2
;;;
;;; Program  ---> (letrec ([label (lambda () Tail)]*) Tail)
;;; Tail     ---> (Triv)
;;;            |  (begin Effect* Tail)
;;; Effect   ---> (set! Var Triv)
;;;            |  (set! Var (Binop Triv Triv))
;;; Var      ---> reg | fvar
;;; Triv     ---> Var | int | label

(define registers (set 'rax 'rcx 'rdx 'rbx 'rbp 'rsi 'rdi 'r8 'r9 'r10 'r11 'r12 'r13 'r14 'r15))
(define primitives (set '* '+ '- '< '<= '= '>= '> 'add1 'sub1 'zero? 'boolean? 'integer? 'null?
                        'pair? 'procedure? 'vector? 'not 'eq? 'cons 'car 'cdr 'set-car! 'set-cdr!
                        'make-vector 'vector-length 'vector-ref 'vector-set! 'void))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; verify-scheme
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define is-reg?
  (lambda (x)
    (set-member? registers x)))

(define is-fvar?
  (lambda (x)
    (regexp-match #rx"fv[0-9]+" (symbol->string x))))

(define is-label?
  (lambda (x)
    (and (symbol? x) (regexp-match #rx"\\$[0-9]+" (symbol->string x)))))

(define verify-Tail
  (lambda (t)
    (match t
      [`(,triv) #:when (integer? triv)
                (error "Tail cannot be integer")]
      [`(,triv)
       (verify-Triv triv)]
      [`(begin ,effects ... ,tail)
       (map verify-Effect effects)
       (verify-Tail tail)]
      [_ (error t " not valid Tail exp")]
      )))

(define verify-Effect
  (lambda (e)
    (match e
      [`(set! ,v (,op ,t1 ,t2))
       (cond
         [(not (eqv? t1 v)) (error e "var and triv1 are not equal")]
         [(or (is-label? op) (is-label? t1) (is-label? t2)) (error e "either operand or operator is label")]
         [(and (eqv? op '*) (not (is-reg? v))) (error e "is supposed to set reg")]
         [(and (eqv? op 'sra) (or (< t2 0) (> t2 63))) (error e "shift operation is out of bound")]
         [else (verify-Var v) (verify-Triv t1) (verify-Triv t2)])]
      [`(set! ,v ,triv) #:when (or (integer? triv) (is-label? triv))
                        (if (is-reg? v)
                            #t
                            (error e "should have reg"))]
      [`(set! ,v ,triv) ; other cases
       (verify-Var v)
       (verify-Triv triv)]
      )))

(define verify-Var
  (lambda (v)
    (if (or (is-reg? v) (is-fvar? v))
        #t
        (error v "is supposed to be reg or fvar"))))

(define verify-Triv
  (lambda (t)
    (if (or (integer? t) (is-label? t))
        #t
        (verify-Var t))))

;; label instruction: [label (lambda () Tail)]
(define verify-Label
  (lambda (li)
    (match li
      [`(,l (lambda () ,t)) #:when (is-label? l)
                            (verify-Tail t)]
      [_ (error li "invalid label instruction")]
      )))       

(define verify-scheme
  (lambda (prog)
    (match prog
      [`(letrec (,labels ...) ,t)
       (map verify-Label labels)
       (verify-Tail t)
       prog]
      [_ (error prog "invalid format")]
      )))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; expose-frame-var
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define expose-frame-var-Label
  (lambda (li)
    (match li
      [`(,l (lambda () ,tail))
       `(,l (lambda () ,(expose-frame-var-Tail tail)))])))

(define expose-frame-var-Tail
  (lambda (t)
    (match t
      [`(begin ,effects ... ,tail)
       `(begin ,@(map expose-frame-var-Effect effects) ,(expose-frame-var-Tail tail))]
      [`(,triv)
       `(,(expose-frame-var-Triv triv))]
      )))

(define expose-frame-var-Effect
  (lambda (e)
    (match e
      [`(set! ,v (,op ,t1 ,t2))
       `(set! ,(expose-frame-var-Var v) (,op ,(expose-frame-var-Triv t1) ,(expose-frame-var-Triv t2)))]
      [`(set! ,v ,t)
       `(set! ,(expose-frame-var-Var v) ,(expose-frame-var-Triv t))]
      )))

(define expose-frame-var-Var
  (lambda (v)
    (if (is-reg? v)
        v
        `(disp rbp ,(string->number (car (regexp-match #rx"[0-9]+$" (symbol->string v))))))))

(define expose-frame-var-Triv
  (lambda (t)
    (if (or (integer? t) (is-label? t))
        t
        (expose-frame-var-Var t))))

(define expose-frame-var
  (lambda (prog)
    (match prog
      [`(letrec (,label-instrs ...) ,tail)
       `(letrec ,(map expose-frame-var-Label label-instrs) ,(expose-frame-var-Tail tail))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; flatten-program
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define flatten-program-Label
  (lambda (li)
    (match li
      [`(,lname (lambda () ,tail))
       `(,lname ,@(flatten-program-Tail tail))])))

(define flatten-program-Tail
  (lambda (t)
    (match t
      [`(begin ,effects ... ,tail)
       `(,@(map flatten-program-Effect effects) ,(flatten-program-Tail tail))]
      [`(,triv)
       `(jump ,(flatten-program-Triv triv))]
      )))

(define flatten-program-Effect
  (lambda (e)
    (match e
      [`(set! ,v (,op ,t1 ,t2))
       `(set! ,(flatten-program-Var v) (,op ,(flatten-program-Triv t1) ,(flatten-program-Triv t2)))]
      [`(set! ,v ,t)
       `(set! ,(flatten-program-Var v) ,(flatten-program-Triv t))]
      )))

;; Nothing need to be changed for var
(define flatten-program-Var
  (lambda (v)
    v))

(define flatten-program-Triv
  (lambda (t)
    (if (or (integer? t) (is-label? t))
        t
        (flatten-program-Var t))))

(define flatten-program
  (lambda (prog)
    (match prog
      [`(letrec (,label-instrs ...) ,tail)
       `(code ,(flatten-program-Tail tail) ,@(my-map flatten-program-Label label-instrs) )])))

(define my-map
  (lambda (f lst)
    (if (null? lst)
        '()
        (append (f (car lst)) (my-map f (cdr lst))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Test
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;(define driver
;  (lambda (program)
;    (with-output-to-file "t.s" (lambda ()
;                                 (generate-x86-64 (verify-scheme program))))))

(flatten-program
(expose-frame-var
'(letrec ([f$1 (lambda ()
                (begin
                 
                  (set! fv0 rax)
                  (set! rax (+ rax rax))
                  (set! rax (+ rax fv0))
                  (r15)))])
  (begin
    (set! rax 17)
    (f$1)))))