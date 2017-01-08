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
       (match t
         [`(begin ,effects ... ,tail)
          (map expose-basic-blocks-Label (expose-basic-blocks-Effects t))]
         [`(if ,p ,t1 ,t2)
          (let* ([label1 (label-generate)]
                 [label2 (label-generate)]
                 [t1-label-instr (expose-basic-blocks-Label `(,label1 (lambda () ,t1)))]
                 [t2-label-instr (expose-basic-blocks-Label `(,label2 (lambda () ,t2)))])
            (match p
              [`(true) `((,lname (lambda () (,label1))) ,@t1-label-instr)]
              [`(false) `((,lname (lambda () (,label2))) ,@t2-label-instr)]
              [`(if ,pcnd ,pthn ,pels)
               (let ([thn-label (label-generate)]
                     [els-label (label-generate)])
                 `(,@(expose-basic-blocks-Label `(,lname (lambda () (if ,pcnd (,thn-label) (,els-label)))))
                   ,@(expose-basic-blocks-Label `(,thn-label (lambda () (if ,pthn (,label1) (,label2)))))
                   ,@(expose-basic-blocks-Label `(,els-label (lambda () (if ,pels (,label1) (,label2)))))
                   ,@t1-label-instr ,@t2-label-instr))]
              [`(begin ,es ... ,pr)
               (let ([pred-label (label-generate)])
                 `(,(expose-basic-blocks-Label `(,lname (lambda () (begin ,@es (,pred-label)))))
                   ,@(expose-basic-blocks-Label `(,pred-label (lambda () (if ,pr (,label1) (,label2)))))
                   ,@t1-label-instr ,@t2-label-instr))]))]
         [`(,triv) #:when (is-label? triv)
          ;`((,lname (lambda () ,(expose-basic-blocks-Triv triv))))]
          `((,triv))]
         )])))

(define expose-basic-blocks-Effects
  (lambda (t)
    (match t
      [`(begin ,es ... ,tail)
      [`(nop) '()]
      [`(set! ,v (,op ,t1 ,t2))
       e]
      [`(set! ,v ,t)
       e]
      [`(if ,p ,e1 ,e2)
       `(if ,(expose-basic-blocks-Pred p) ,(expose-basic-blocks-Effect e1) ,(expose-basic-blocks-Effect e2))]
      [`(begin ,es ... ,e)
       `(begin ,@(my-map-1 expose-basic-blocks-Effect es) ,(expose-basic-blocks-Effect e))]
      )))

(define expose-basic-blocks-Loc
  (lambda (t)
    t))

;; No syntax check
(define expose-basic-blocks-Triv
  (lambda (t)
    t))

(define expose-basic-blocks
  (lambda (prog)
    (match prog
      [`(letrec (,label-instrs ...) ,b)
       `(letrec ,(my-map-1 expose-basic-blocks-Label label-instrs) ,(expose-basic-blocks-Body b))])))
      
