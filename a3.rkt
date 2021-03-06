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
;;; Program  ---> (letrec ([label (lambda () Body)]*) Body)
;;; Body     ---> (locate ([uvar Loc]*) Tail)
;;; Tail     ---> (Triv)
;;;            |  (if Pred Tail Tail)
;;;            |  (begin Effect* Tail)
;;; Pred     ---> (true)
;;;            |  (false)
;;;            |  (relop Triv Triv)
;;;            |  (if Pred Pred Pred)
;;;            |  (begin Effect* Pred)
;;; Effect   ---> (nop)
;;;            |  (set! Var Triv)
;;;            |  (set! Var (binop Triv Triv))
;;;            |  (if Pred Effect Effect)
;;;            |  (begin Effect* Effect)
;;; Loc      ---> reg | fvar
;;; Var      ---> uvar | Loc
;;; Triv     ---> Var | int | label

(define registers (set 'rax 'rcx 'rdx 'rbx 'rbp 'rsi 'rdi 'r8 'r9 'r10 'r11 'r12 'r13 'r14 'r15))
(define primitives (set '* '+ '- '< '<= '= '>= '> 'add1 'sub1 'zero? 'boolean? 'integer? 'null?
                        'pair? 'procedure? 'vector? 'not 'eq? 'cons 'car 'cdr 'set-car! 'set-cdr!
                        'make-vector 'vector-length 'vector-ref 'vector-set! 'void))
(define uvar-pat "\\.[0-9]+")
(define label-pat "\\$[0-9]+")
(define fvar-pat "fv[0-9]")
(define label-prefix-list `("a" "c" "f" "j"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 4.1 verify-scheme
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
      [`(nop) #t]
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
;;; 4.2 finalize-locations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; A grammar for the output of this pass is shown below:

;;; Program  ---> (letrec ([label (lambda () Tail)]*) Tail)
;;; Tail     ---> (Triv)
;;;            |  (if Pred Tail Tail)
;;;            |  (begin Effect* Tail)
;;; Pred     ---> (true)
;;;            |  (false)
;;;            |  (relop Triv Triv)
;;;            |  (if Pred Pred Pred)
;;;            |  (begin Effect* Pred)
;;; Effect   ---> (nop)
;;;            |  (set! Var Triv)
;;;            |  (set! Var (binop Triv Triv))
;;;            |  (if Pred Effect Effect)
;;;            |  (begin Effect* Effect)
;;; Loc      ---> reg | fvar
;;; Triv     ---> Loc | int | label

(define empty-env '())

(define look-up
  (lambda (x env)
    (if (null? env)
        (error "Not exist in env" x)
        (if (eqv? x (caar env))
            (cadar env)
            (look-up x (cdr env))))))

(define my-map-1
  (lambda (f lst env)
    (if (null? lst)
        '()
        (cons (f (car lst) env) (my-map-1 f (cdr lst) env)))))

(define finalize-locations-Label
  (lambda (li env)
    (match li
      [`(,l (lambda () ,b))
       `(,l (lambda () ,(finalize-locations-Body b env)))])))

(define finalize-locations-Body
  (lambda (b env)
    (match b
      [`(locate ,uvar-loc-list ,t)
       (finalize-locations-Tail t (append uvar-loc-list env))])))

(define finalize-locations-Tail
  (lambda (t env)
    (match t
      [`(begin ,effects ... ,tail)
       `(begin ,@(my-map-1 finalize-locations-Effect effects env) ,(finalize-locations-Tail tail env))]
      [`(if ,p ,t1 ,t2)
       `(if ,(finalize-locations-Pred p env) ,(finalize-locations-Tail t1 env) ,(finalize-locations-Tail t2 env))]
      [`(,triv)
       `(,(finalize-locations-Triv triv env))]
      )))

(define finalize-locations-Pred
  (lambda (p env)
    (match p
      [`(true) p]
      [`(false) p]
      [`(,relop ,t1 ,t2) #:when (set-member? primitives relop)
       `(,relop ,(finalize-locations-Triv t1 env),(finalize-locations-Triv t2 env))]
      [`(if ,p ,pthn ,pels)
       `(if ,(finalize-locations-Pred p env) ,(finalize-locations-Pred pthn env) ,(finalize-locations-Pred pels env))]
      [`(begin ,es ... ,p)
       `(begin ,@(my-map-1 finalize-locations-Effect es env) ,(finalize-locations-Pred p env))])))

(define finalize-locations-Effect
  (lambda (e env)
    (match e
      [`(nop) e]
      [`(set! ,v (,op ,t1 ,t2))
       `(set! ,(finalize-locations-Var v env) (,op ,(finalize-locations-Triv t1 env) ,(finalize-locations-Triv t2 env)))]
      [`(set! ,v ,t)
       `(set! ,(finalize-locations-Var v env) ,(finalize-locations-Triv t env))]
      [`(if ,p ,e1 ,e2)
       `(if ,(finalize-locations-Pred p env) ,(finalize-locations-Effect e1 env) ,(finalize-locations-Effect e2 env))]
      [`(begin ,es ... ,e)
       `(begin ,@(my-map-1 finalize-locations-Effect es env) ,(finalize-locations-Effect e))]
      )))

(define finalize-locations-Var
  (lambda (v env)
    (if (regexp-match #rx"\\.[0-9]+$" (symbol->string v))
        (look-up v env)
        v)))

(define finalize-locations-Triv
  (lambda (t env)
    (if (or (integer? t) (is-label? t))
        t
        (finalize-locations-Var t env))))

(define finalize-locations
  (lambda (prog)
    (match prog
      [`(letrec (,label-instrs ...) ,b)
       `(letrec ,(my-map-1 finalize-locations-Label label-instrs empty-env) ,(finalize-locations-Body b empty-env))])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 4.3 expose-frame-var (simple tree search)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define expose-frame-var-Var
  (lambda (v)
    (if (and (symbol? v) (regexp-match #rx"fv[0-9]+$" (symbol->string v)))
        `(disp rbp ,(string->number (car (regexp-match #rx"[0-9]+$" (symbol->string v)))))
        v)))

(define expose-frame-var
  (lambda (prog)
    (if (list? prog)
        (map expose-frame-var prog)
        (expose-frame-var-Var prog))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 4.4 expose-basic-blocks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(expose-frame-var
(finalize-locations
`(letrec ([f$1 (lambda ()
                  (locate ([x.1 r8] [y.2 r9])
                          (if (if (= x.1 1) (true) (> y.2 1000))
                              (begin (set! rax y.2) (r15))
                              (begin
                                (set! y.2 (* y.2 2))
                                (set! rax x.1)
                                (set! rax (logand rax 1))
                                (if (= rax 0) (set! y.2 (+ y.2 1)) (nop)) (set! x.1 (sra x.1 1))
                                (f$1)))))])
          (locate () (begin (set! r8 3) (set! r9 10) (f$1))))))