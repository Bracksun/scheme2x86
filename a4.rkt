#lang racket

(require "a3.rkt")

;; Grammar of input
;; Program −> (letrec ([label (lambda () Body)]*) Body)
;; Body −> (locals (uvar*) Tail)
;; Tail −> (Triv Loc*)
;; 	 | (if Pred Tail Tail)
;; 	 | (begin Effect* Tail)
;; Pred −> (true)
;; 	 | (false)
;; 	 | (relop Triv Triv)
;; 	 | (if Pred Pred Pred)
;; 	 | (begin Effect* Pred)
;; Effect −> (nop)
;; 	   | (set! Var Triv)
;; 	   | (set! Var (binop Triv Triv))
;; 	   | (if Pred Effect Effect)
;; 	   | (begin Effect* Effect)
;; Loc −> reg | fvar
;; Var −> uvar | Loc
;; Triv −> Var | int | label

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; uncover-register-conflict
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Grammar for the output of this pass
;; Only changed to Body
;; Body --> (locals (uvar*)
;;	      (register-rconflict conflict-graph Tail))

;; conflict-graph: ((a r15 rbp b)
;;                  (b r15 rbp a c)
;;                  (c b r15 rbp))

;; make-cg: make hash table for conflict graph
(define make-cg
  (lambda (var-lst)
    
  (define make-cg1
    (lambda (lst cg-ht)
      (if (null? lst)
          cg-ht
          (begin (hash-set! cg-ht (car lst) (set))
                 (make-cg1 (cdr lst) cg-ht)))))
    (make-cg1 var-lst (make-hash))))

;; cg utilities (not sure cg-ht should be return value or global struct)
(define cg-update
  (lambda (cg-ht k set)
    (if (hash-has-key? cg-ht k)
        (begin (hash-set! cg-ht (set-union (hash-ref cg-ht k) (set-remove set k)))
               cg-ht)
        cg-ht)))
(define cg-updates
  (lambda (cg-ht set1 set2)
    (if (null? set1)
        cg-ht
        (cg-updates (cg-update cg-ht (car set1) set2) (cdr set1) set2))))
    

(define uncover-register-conflict-effect
  (lambda (eff live-set)
    (match eff
      [`(set! ,v (,binop ,t1 ,t2))
       ]
      [`(set! ,v ,t)
       ]
      [`(if ,cond ,thn ,els)
       (let ([thn-live-set (uncover-register-conflict-effect thn live-set)]
             [els-live-set (uncover-register-conflict-effect els live-set)]) 
         (uncover-register-conflict-pred cond (set-union thn-live-set els-live-set)))]
      ['begin live-set]
      ['(nop) live-set]
)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; test
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define p
  '(letrec ()
     (locals (a b c)
             (begin
               (set! a r8)
               (set! b fv0)
               (set! c (+ a 2))
               (if (< c 0)
                   (nop)
                   (set! c (+ c b)))
               (set! rax (+ c 1))
               (r15 rax rbp)))))
  
