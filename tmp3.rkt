#lang racket
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 4.4 expose-basic-blocks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define registers (set 'rax 'rcx 'rdx 'rbx 'rbp 'rsi 'rdi 'r8 'r9 'r10 'r11 'r12 'r13 'r14 'r15))
(define primitives (set '* '+ '- '< '<= '= '>= '> 'add1 'sub1 'zero? 'boolean? 'integer? 'null?
                        'pair? 'procedure? 'vector? 'not 'eq? 'cons 'car 'cdr 'set-car! 'set-cdr!
                        'make-vector 'vector-length 'vector-ref 'vector-set! 'void))
(define uvar-pat "\\.[0-9]+")
(define label-pat "\\$[0-9]+")
(define fvar-pat "fv[0-9]")
(define label-prefix-list `("a" "c" "f" "j"))

(define is-label?
  (lambda (x)
    (and (symbol? x) (regexp-match #rx"\\$[0-9]+" (symbol->string x)))))

;;; A grammar for the output of this pass is shown below:

;;; Program  ---> (letrec ([label (lambda () Tail)]*) Tail)
;;; Tail     ---> (Triv)
;;;            |  (if (relop Triv Triv) (,label) (,label))
;;;            |  (begin Effect* Tail)
;;; Effect   ---> (set! Loc Triv)
;;;            |  (set! Loc (binop Triv Triv))
;;; Loc      ---> reg | dis-opnd
;;; Triv     ---> Loc | int | label

; helper function -- label-generate
(define n 1)
(define label-generate
  (lambda ()
    (let ([len (length label-prefix-list)])
      (set! n (+ n 1))
      (string->symbol (string-append (list-ref label-prefix-list (random len))
                                     "$" (number->string n))))))
;; Main part
(define expose-basic-blocks-Label
  (lambda (li)
    (match li
      [`(,lname (lambda () ,t))
       (let-values ([(ret bindings) (expose-basic-blocks-Tail t)])
         `((,lname (lambda () ,ret)) ,@bindings))])))


;; Tail
;; return -- value pair: new-tail && new-bindings
(define expose-basic-blocks-Tail
  (lambda (t)
       (match t
         [`(begin ,effects ... ,tail)
          (let-values ([(effs label-bindings) (expose-basic-blocks-Effects `(,@effects ,tail))])
            (values (if (eq? 1 (length effs)) (car effs) `(begin ,@effs))
                    label-bindings))]
         [`(if ,p ,t1 ,t2)
          (let* ([label1 (if (is-label? (car t1)) (car t1) (label-generate))]
                 [label2 (if (is-label? (car t2)) (car t2) (label-generate))]
                 [t1-label-binding (if (is-label? (car t1)) '() (expose-basic-blocks-Label `(,label1 (lambda () ,t1))))]
                 [t2-label-binding (if (is-label? (car t2)) '() (expose-basic-blocks-Label `(,label2 (lambda () ,t2))))])
            (match p
              [`(true) (values `(,label1) t1-label-binding)]
              [`(false) (values `(,label2) t2-label-binding)]
              [`(if ,pcnd ,pthn ,pels)
               (let ([thn-label (label-generate)]
                     [els-label (label-generate)])
                 (let-values ([(t-ret bindings) (expose-basic-blocks-Tail `(if ,pcnd (,thn-label) (,els-label)))])
                   (values t-ret
                           `(,@bindings
                             ,@(expose-basic-blocks-Label `(,thn-label (lambda () (if ,pthn (,label1) (,label2)))))
                             ,@(expose-basic-blocks-Label `(,els-label (lambda () (if ,pels (,label1) (,label2)))))
                             ,@t1-label-binding ,@t2-label-binding))))]
              [`(begin ,es ... ,pr)
               (let ([pred-label (label-generate)])
                 (let-values ([(ret bindings) (expose-basic-blocks-Tail `(begin ,@es (,pred-label)))])
                   (values ret `(,bindings
                                 ,@(expose-basic-blocks-Label `(,pred-label (lambda () (if ,pr (,label1) (,label2)))))
                                 ,@t1-label-binding ,@t2-label-binding))))]
              [`(,relop ,triv1 ,triv2)
               (values `(if ,p (,label1) (,label2)) `(,@t1-label-binding ,@t2-label-binding))]))]
         [`(,triv) #:when (is-label? triv)
          (values `(,triv) '())]
         )))

;; flatten effects
;; return -- value pair: rest of effects && label instructions
(define expose-basic-blocks-Effects
  (lambda (tail-effect)
    (match tail-effect
      [`(,es ... ,tail)
       (if (null? es)
           (values `(,tail) '())
           (match (car es)
             [`(nop) (expose-basic-blocks-Effects `(,@(cdr es) ,tail))]
             [`(set! ,v (,op ,t1 ,t2))
              (let-values ([(e-rest label-binding) (expose-basic-blocks-Effects `(,@(cdr es) ,tail))])
                (values (cons (car es) e-rest) label-binding))]
             [`(set! ,v ,t)
              (let-values ([(e-rest label-binding) (expose-basic-blocks-Effects `(,@(cdr es) ,tail))])
                (values (cons (car es) e-rest) label-binding))]
             [`(if ,p ,e1 ,e2)
              (let ([e1-label (label-generate)]
                    [e2-label (label-generate)]
                    [rest-label (label-generate)])
                (values `((if ,p (,e1-label) (,e2-label)))
                         (append (expose-basic-blocks-Label `(,e1-label (lambda () (begin ,e1 (,rest-label)))))
                                 (expose-basic-blocks-Label `(,e2-label (lambda () (begin ,e2 (,rest-label)))))
                                 (expose-basic-blocks-Label `(,rest-label (lambda () (begin ,@(cdr es) ,tail)))))))]
             [`(begin ,effs ... ,e)
              (expose-basic-blocks-Effects `(,@effs ,e ,@(cdr es) ,tail))]))])))


(define expose-basic-blocks
  (lambda (prog)
    (match prog
      [`(letrec (,label-instrs ...) ,tail)
       (let-values ([(ret tbindings) (expose-basic-blocks-Tail tail)])
       `(letrec ,(append (car (map expose-basic-blocks-Label label-instrs)) tbindings) ,ret))])))
      
;(expose-basic-blocks
; '(letrec ([f$1
;           (lambda ()
;             (if (if (= r8 1) (true) (> r9 1000))
;               (begin (set! rax r9) (r15))
;               (begin
;                 (set! r9 (* r9 2))
;                 (set! rax r8)
;                 (set! rax (logand rax 1))
;                 (if (= rax 0) (set! r9 (+ r9 1)) (nop))
;                 (set! r8 (sra r8 1))
;                 (f$1))))])
;   (begin (set! r8 3) (set! r9 10) (f$1))))

(expose-basic-blocks
 '(letrec ([f$1
           (lambda ()
             (if (if (= r8 1) (true) (> r9 1000))
               (begin (set! rax r9) (r15))
               (begin
                 (set! r9 (* r9 2))
                 (set! rax r8)
                 (set! rax (logand rax 1))
                 (if (= rax 0) (set! r9 (+ r9 1)) (nop))
                 (set! r8 (sra r8 1))
                 (f$1))))])
   (begin (set! r8 3) (set! r9 10) (if (= rax 0) (set! r9 (+ r9 1)) (nop)) (f$1))))
