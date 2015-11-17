#lang racket
(require test-engine/racket-tests)

;; Curried Functions let you easily produce
;; named concrete instantiations of the
;; abstract function by partially applying
;; the function
(define curried-map (curry map))
(define curried-fold (curry foldl))
(define curried-filter (curry filter))

;; do an element by element product of two lists
(define by-elem-pro (curried-map (lambda (l r) (* l r))))
;; sum the contents of a list
(define sum-list (curried-fold (lambda (e sum) (+ e sum)) 0))

;; vector dot product on lists
(define (dot-pro lhs rhs)
  (sum-list (by-elem-pro lhs rhs)))

;; Example
(define a (list 1 2 3 4 5))
(define b (list 1 2 3 4 5))
(check-expect (+ 1 4 9 16 25) (dot-pro a b))

;; Local identifiers/variables
;; They aid in readability and allow
;; you to avoid repeated computation in
;; a purely functional world (compute once and name)

;; The Cosine-Sim is a measure of similarity
;; between two vectors
(define (cos-sim lhs rhs)
  (let ((len-lhs (sqrt (dot-pro lhs lhs)))
        (len-rhs (sqrt (dot-pro rhs rhs))))
    (/ (dot-pro lhs rhs) (* len-lhs len-rhs))))

;; cos-sim only gets computed once but used up to
;; 4 times
(define (compare-vecs lhs rhs)
  (let ((sim (cos-sim lhs rhs)))
    (cond ((= sim 1) "co-directional")
          ((= sim -1) "opposite direction")
          ((= sim 0) "orthogonal")
          (else (string-append "differs by " (~a sim))))))

;; (let/let*/letr ((id val) ...) body)
;; let --> parallel binding -> ids are distinct.. binds values in body only
;; let* --> sequential binding -> ids are bound in subsequent values and finally the body
;; letrec --> recursive binding -> let* but ids are bound in their own values as well
        

(test)