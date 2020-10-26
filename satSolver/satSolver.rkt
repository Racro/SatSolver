#lang racket

(require "utilities.rkt")

(define assign #hash())

; Fill in your code here. Should finally define a function
; called dpll which returns true or false. Should additionally
; store the satisfying assignment in the variable assign.

(define (unit-prop l l1)      ;l1 = (list )   ;iske arguments edit karoon kya?
  (define (helper list1)
    (define (pass-single-clause lst)
      (cond [(null? lst) lst]
            [(= (length (car lst)) 1)
             (begin (set! l1 (if (> (caar lst) 0) (cons (cons (caar lst) #t) l1) (cons (cons (abs (caar lst)) #f) l1)))
                    (car lst))]
            (else (pass-single-clause (cdr lst)))))
    (define (filter-single-clause lst k)
      (cond [(null? lst) (list )]
            [(equal? (car lst) k) (filter-single-clause (cdr lst) k)]
            [(init (car lst) (car k)) (cons (remove (- 0 (car k)) (car lst)) (filter-single-clause (cdr lst) k))]
            [(init (car lst) (- 0 (car k))) (filter-single-clause (cdr lst) k)]
            (else (cons (car lst) (filter-single-clause (cdr lst) k)))))
    (let ([pass (pass-single-clause list1)])
      (cond [(null? pass) list1]
            (else (helper (filter-single-clause list1 pass))))))
  (let ([dummy (helper l)])
    (cons l1 dummy)))

(define (init l k)
  (cond [(null? l) #f]
        [(= (car l) (- 0 k)) #t]
        (else (init (cdr l) k))))

(define (init-list l1 l2)
  (cond [(null? l1) #f]
        [(equal? (car l1) l2) #t]
        (else (init-list (cdr l1) l2))))

(define (list-of-literals lst)
  (remove-duplicates (append* lst)))

(define (remove-all k l)
  (cond [(null? l) (list )]
        [(= k (car l)) (remove-all k (cdr l))]
        (else (cons (car l) (remove-all k (cdr l))))))
        
(define (lit-elimination l l-dummy)      ;l-dummy=(list )
  (define (helper1)
    (define (refined-list lt)
      (cond [(null? lt) (list )]
            [(init (cdr lt) (car lt)) (refined-list (remove-all (car lt) (remove-all (- 0 (car lt)) lt)))]
            (else (cons (car lt) (refined-list (cdr lt))))))
    (let ([ls (refined-list (list-of-literals l))])
      (begin (set! l-dummy (map (lambda (x) (if (> x 0) (cons x #t) (cons (abs x) #f))) ls))
             (define (final-ans l2)
               (define (helper l1 k)
                 (cond [(null? l1) (final-ans (cdr l2))] 
                       [(init (car l1) (- 0 k)) (begin (set! l (remove (car l1) l)) (helper (cdr l1) k))]
                       (else (helper (cdr l1) k))))
               (cond [(null? l2) l]
                     (else (helper l (car l2)))))
             (final-ans ls))))
  (let ([dummy (helper1)])
    (cons l-dummy dummy)))

(define (dpll-dummy F)
  (let ([unit-dummy (unit-prop F (list ))])
    (let ([lit-eli (lit-elimination (cdr unit-dummy) (list ))])
      (let ([result1 (cdr lit-eli)]
            [list1 (car unit-dummy)]
            [list2 (car lit-eli)])
        (cond [(null? result1) (cons (append list1 list2) (cons result1 #t))]
              [(init-list result1 (list )) (cons (append list1 list2) (cons result1 #f))]
              (else (cons (append list1 list2) (cons result1 0))))))))

(define (list-of-pos-lit l)
  (remove-duplicates (map (lambda (x) (abs x)) (append* l))))

(define (flatten l)
  (cond [(equal? l #f) (list #f)]
        [(null? l) (list )]
        [(list? (car l)) (append (flatten (car l)) (flatten (cdr l)))]
        (else (cons (car l) (flatten (cdr l))))))

(define (anonymous F-new-t l-t F-new-f l-f)   ;(l-t,l-f=(list ) ; l2=(list-of-pos-lit))
  (define (refine-F lst k val)
    (cond [(null? lst) (list )]
          [(and (equal? val #t) (init (car lst) (- 0 (car k)))) (refine-F (cdr lst) k val)]
          [(and (equal? val #f) (init (car lst) (car k))) (refine-F (cdr lst) k val)]
          [(and (equal? val #t) (init (car lst) (car k)))
           (cons (remove (- 0 (car k)) (car lst)) (refine-F (cdr lst) k val))]
          [(and (equal? val #f) (init (car lst) (- 0 (car k))))
           (cons (remove (car k) (car lst)) (refine-F (cdr lst) k val))]
          (else (cons (car lst) (refine-F (cdr lst) k val)))))
  (let ([d-t (dpll-dummy F-new-t)]
        [d-f (dpll-dummy F-new-f)])
    (let ([oper-t (cdr (cdr d-t))]
          [oper-f (cdr (cdr d-f))]
          [list-t (car (cdr d-t))]
          [list-f (car (cdr d-f))]
          [ans-t (car d-t)]
          [ans-f (car d-f)])
      (let ([pos-t (list-of-pos-lit list-t)]
            [pos-f (list-of-pos-lit list-f)])
     ; (displayln pos-t) (displayln pos-f)
        (begin (set! l-t (append ans-t l-t)) (set! l-f (append ans-f l-f))
           
               (cond ;[(null? l2) #f]
                 [(equal? #t oper-t) (cons #t l-t)]
                 [(equal? #t oper-f) (cons #t l-f)]
                 [(equal? #f oper-t) (if (equal? #f oper-f) #f
                                         (anonymous (refine-F list-f (list (car pos-f)) #t) (cons (cons (car pos-f) #t) l-f)
                                                    (refine-F list-f (list (car pos-f)) #f) (cons (cons (car pos-f) #f) l-f)))]
                 [(equal? #f oper-f) (if (equal? #f oper-t) #f
                                         (anonymous (refine-F list-t (list (car pos-t)) #t) (cons (cons (car pos-t) #t) l-t)
                                                    (refine-F list-t (list (car pos-t)) #f) (cons (cons (car pos-t) #f) l-t)))]
                 [(equal? list-t list-f)
                  (anonymous (refine-F list-t (list (car pos-t)) #t) (cons (cons (car pos-f) #t) l-t)
                             (refine-F list-f (list (car pos-f)) #f) (cons (cons (car pos-f) #f) l-f))]
                 (else
                  (let ([l1 (anonymous (refine-F list-t (list (car pos-t)) #t) (cons (cons (car pos-t) #t) l-t)
                                           (refine-F list-t (list (car pos-t)) #f) (cons (cons (car pos-t) #f) l-t))])
                   (cond [(equal? #f l1) (anonymous (refine-F list-f (list (car pos-f)) #t) (cons (cons (car pos-f) #t) l-f)
                                          (refine-F list-f (list (car pos-f)) #f) (cons (cons (car pos-f) #f) l-f))]
                         (else l1))))))))))

                  


(define (dpll T)
  (define F (anti-parse T))
  (set! assign #hash())
  (define (update-hash l)
    (cond [(null? l) assign]
          (else (begin (set! assign (dict-set assign (caar l) (cdr (car l)))) (update-hash (cdr l))))))
  (define (helper anon)
    (cond ;[(null? anon) (begin (displayln #f) assign)]
          [(equal? anon #f) anon]
          ;[(equal? (car anon) #f) (helper (cdr anon))]
          [(equal? (car anon) #t) (begin (update-hash (cdr anon)) (car anon))]))
  (helper (anonymous F (list ) F (list ))))

(define (anti-parse t)
  (cond [(Not? t) (list (list (* -1 (Var-lit (Not-e t)))))]
        [(Var? t) (list (list (Var-lit t)))]
        [(Or? t) (list (append* (append (anti-parse (Or-x t)) (anti-parse (Or-y t)))))]
        [(And? t) (append (anti-parse (And-x t)) (anti-parse (And-y t)))]))


