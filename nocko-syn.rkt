;;  nocko.rkt
;;  2024
;;  Nock 4K in miniKanren
;;  Racket v8.12

#lang racket

(require minikanren)
(require minikanren/numbers)

;"A noun is an atom or a cell.  An atom is a natural number.  A cell
;is an ordered pair of nouns." - these translate directly into mK:

(define (nouno i)
  (conde
   [(atomo i)]
   [(cello i)]))

(define (atomo i)
  (fresh (d)
	 (== `(nat . ,d) i)
	 (nato d)))

(define (nato i)
  (fresh (d)
	 (conde
	  [(== '(0) i)]
	  [(== '(1) i)]
	  [(== `(0 . ,d) i)
	   (=/= '(0) d)
	   (nato d)]
	  [(== `(1 . ,d) i)
	   (=/= '(0) d)
	   (nato d)])))
   
(define (cello i)
  (fresh (a d)
	 (== `(,a ,d) i)
	 (nouno a)
	 (nouno d)))

;Reduce by the first matching pattern; variables match any noun.

;A sequential pattern match implicitly accumulates conditions as each
;previous match clause fails. To replicate the behavior of a
;sequential pattern match in a pure relational language, fully
;disjunct match criteria must be explicitly encoded. This is
;straightforward for the supermajority of reduction expressions
;(redexes), but will be a point of discussion late in the
;implementation. The directive to "reduce by the first matching
;pattern" suggests a direct term rewriting approach; this is adopted,
;though an alternative structure of the program using functions
;instead of expression tags is presented.

;nock(a)             *a

;The first design decision is whether to build a single (nocko)
;procedure, or separate the nops (nock operations) into individual
;relations, and if so, with what grouping.  There is also the choice
;between translating `nock(a)` as an expression to be evaluated by an
;interpreter (the `nevalo` design) or considerating `nock` to be the
;name of the evaluator (the `nocko` design). The latter is chosen.

;We begin with a monolithic `nocko` relation, using pattern matching
;on quoted expressions to perform the redexes.

;(this is actually the functional nocko)
(define (nocko i o) 
  (fresh (a)
         (raso i a)
         (taro a o)))

(define (wuto i o)
  (fresh (a b)
	 (conde
	  [ (== `[,a ,b] i) (== 0 o) ]
	  [ (atomo i)       (== 1 o) ]
	  )))

(define (luso i o)
  (fresh (a b)
	 (conde
	  [ (== `[,a ,b] i) (== `[lus ,i] o) ]
	  [ (atomo i)       (nadd1o i o) ] ;requires defining nadd1o for atoms
	  )))

(define (tiso i o)
  (fresh (a b)
	 (conde
	  [ (== `[,a ,a] i)           (== 0 o) ]
	  [ (== `[,a ,b] i) (=/= a b) (== 1 o) ]
	  )))

(define (faso i o)
  (fresh (a b ind num res n)
	 (conde
	  [ (== `[(nat 1) ,a] i)        (== a o) ]
	  [ (== `[(nat 0 1) [,a ,b]] i) 
	    (nouno a) (nouno b)         (== a o) ] ;nouno check prevents [,a ,b] === [nat num]
	  [ (== `[(nat 1 1) [,a ,b]] i) 
	    (nouno a) (nouno b)         (== b o) ]
	  [ (== `[,ind ,b] i)
	    (=/= '(nat 0) ind)
	    (=/= '(nat 0 1) ind)
	    (npluso a a ind)            (faso `[,a ,b] res) (faso `[(nat 0 1) ,res] o) ]
	  [ (== `[,ind ,b] i)
	    (=/= '(nat 1) ind)
	    (=/= '(nat 1 1) ind)
	    (npluso n '(nat 1) ind) 
	    (npluso a a n)              (faso `[,a ,b] res) (faso `[(nat 1 1) ,res] o) ]
;	  [ (== a i) ]  
	       ;^this is the first instance of a spec mandated
	       ;irreducible rule. wut, lus, and tis, despite only
	       ;operating on a subset of all nouns, do not specify an
	       ;error case; any error handling may be presumed to be
	       ;at the implementer's discretion. However, irreducible
	       ;expressions involving fas, hax, and tar must engage
	       ;with the spec, which calls for them to loop. With
	       ;nocko, employing miniKanren semantics, this looping
	       ;may be mapped to divergence, the lack of a resolution
	       ;to the relational Nock expression; the <x>-loop
	       ;relations implement this (TODO: Implement looping
	       ;relations). The mainline relations instead produce a
	       ;more opinionated reponse, by converging to the empty
	       ;resolution list.
	  )))

#|
Partitioning the domain of fas: all RHS rules must be shapes that converge to T, by either producing a unification, or positively failing to unify, thus producing the empty list. All LHS shapes that yield |_ are then redundant, but may be specified positively, and produce positive failure.
/a
a: atom -> |_
a: cell -> /[b c]
 b: atom ->
  b: 0 -> |_
  b: 1 -> T
  b: >1 ->
   c: atom -> |_
   c: cell -> T
 b: cell -> |_
|#

(define (haxo i o) 
  (fresh (a b ind c n res)
         (conde
          [ (== `[(nat 1) [,a ,b]] i) 
            (nouno a) (nouno b)                 (== a o) ]
          [ (== `[,ind [,b ,c]] i)
            (nouno b) (nouno c)
            (nadd1o ind n) (npluso a a ind) 
	    (haxo `[,a [[,b ,res] ,c]] o) (faso `[,n ,c] res) ] ;TODO: determine ordering that produces reverse synthesis
          [ (== `[,ind [,b ,c]] i)
            (nouno b) (nouno c)
            (nadd1o n ind) (npluso a a n) 
	    (haxo `[,a [[,b ,res] ,c]] o) (faso `[,n ,c] res) ]
          )))

#|
#a
a: atom -> |_
a: cell -> #[b c]
 c: atom -> |_
 c: cell -> #[b [d e]]
  b: cell -> |_
  b: atom ->
   b: 0 -> |_
   b: >0 -> T
{ potentially necessary for deeper structure analysis, but any failure to unify out be an empty failure, rather than divergence
   b: even -> T 
   b: odd -> T
 } 
|#

(define (taro i o) 
  (fresh (a b c d resa resb resc)
         (conde
          [ (== `[,a [[,b ,c] ,d]] i) 
            (taro `[,a [,b ,c]] resa) 
            (taro `[,a ,d] resb)                                 (== `[,resa ,resb] o) ]

          [ (== `[,a [(nat 0) ,b]] i)                            (faso `[,b ,a] o) ]
          [ (== `[,a [(nat 1) ,b]] i)                            (== b o) ]
          [ (== `[,a [(nat 0 1) [,b ,c]]] i) 
            (taro `[,a ,b] resa)
            (taro `[,a ,c] resb)                                 (taro `[,resa ,resb] o) ]
;;           [ (== `[,a [(num 1 1) ,b]] i) 
;;             (taro `[,a ,b] resa)                                 (wuto resa o) ]
;;           [ (== `[,a [(num 0 0 1) ,b]] i)
;;             (taro `[,a ,b] resa)                                 (luso resa o) ]
;;           [ (== `[,a [(num 1 0 1) [,b ,c]]] i) 
;;             (taro `[,a ,b] resa)
;;             (taro `[,a ,c] resb)                                 (tiso `[,resa ,resb] o) ]

;;           [ (== `[,a [(num 0 1 1) [,b [,c ,d]]]] i) 
;;             (taro `[,a [(num 0 0 1) [num (0 0 1) ,b]]] resa)
;;             (taro `[[(num 0 1) (num 1 1)] [(num 0) ,resa]] resb)
;;             (taro `[[,c ,d] [(num 0) ,resb]] resc)
;;                                                                  (taro `[,a ,resc] o) ]
;;           [ (== `[,a [(num 1 1 1) [,b ,c]]] i) 
;;             (taro `[,a ,b] resa)                                 (taro `[,resa ,c] o) ]
;;           [ (== `[,a [(num 0 0 0 1) [,b ,c]]] i) 
;;             (taro `[,a ,b] resa)                                 (taro `[[,resa ,a] ,c] o) ]
;;           [ (== `[,a [(num 1 0 0 1) [,b ,c]]] i) 
;;             (taro `[,a ,c] resa)                                 (taro `[,resa [(num 0 1) [[(num 0) (num 1)] [(num 0) ,b]]]] o) ]
;;           [ (== `[,a [(num 0 1 0 1) [[,b ,c] ,d]]] i) 
;;             (taro `[,a ,c] resa)
;;             (taro `[,a ,d] resb)                                 (haxo `[,b [,resa ,resb]] o) ]
          
;;           [ (== `[,a [(num 1 1 0 1) [[,b ,c] ,d]]] i)
;;             (taro `[,a ,c] resa)
;;             (taro `[,a ,d] resb)                                 (taro `[[,resa ,resb] [(num 0) (num 3)]] o) ]
;;           [ (== `[,a [(num 1 1 0 1) [,b ,c]]] i)                 (taro `[,a ,c] o) ]

;; ;          [ (numo i) (== 'tar-err o) ]
;;           ;[ (== `[,a . ,b] i) (== 'nat a) (== 1 2) ]
          )))

(define (numo n)
  (fresh (a b c)
         (conde
          [(== '(num ()) n)]
          [(== '(num (1)) n)]
          [(>1o a) (== `(num ,a) n)])))

(define quineo4k '[[[(nat 0) (nat 1)] [[(nat 0) (nat 0 1)] [(nat 0) (nat 1 1)]]] [[(nat 0) (nat 1)] [[(nat 0) (nat 0 1)] [(nat 0) (nat 1 1)]]]])

#|
racket@nocko> (run 1 (q) (nocko quineo4k quineo4k))
'(_.0)
racket@nocko> (run 1 (q) (nocko quineo4k q))
'(((((nat 0) (nat 1)) (((nat 0) (nat 0 1)) ((nat 0) (nat 1 1))))
   (((nat 0) (nat 1)) (((nat 0) (nat 0 1)) ((nat 0) (nat 1 1))))))
racket@nocko> quineo4k
'((((nat 0) (nat 1)) (((nat 0) (nat 0 1)) ((nat 0) (nat 1 1))))
  (((nat 0) (nat 1)) (((nat 0) (nat 0 1)) ((nat 0) (nat 1 1)))))
racket@nocko> (car (run 1 (q) (nocko quineo4k q)))
'((((nat 0) (nat 1)) (((nat 0) (nat 0 1)) ((nat 0) (nat 1 1))))
  (((nat 0) (nat 1)) (((nat 0) (nat 0 1)) ((nat 0) (nat 1 1)))))
racket@nocko> (equal? quineo4k (car (run 1 (q) (nocko quineo4k q))))
#t
|#

#|
*a
a: atom -> |_
a: cell -> *[b c]
 b: 

TODO: instrument taro-diag, check that no case matches two RHS patterns.

noun shape case analysis: any case which yields |_ should fail, cases yielding T may fail later in evaluation.
*a
a: noun ->
  a: atom -> |_
a: cell -> 
*[b c]
  b: noun -> T
c: atom -> |_
c: cell -> 
*[b [d e]]
    d: atom >=12 -> |_
  d: cell -> *[b [[f g] e]] -> T
d: atom <12 -> T
d: 0 -> 
  e: noun -> T
d: 1 -> 
  e: noun -> T
d: 2 ->
  e: atom -> |_
e: cell -> T
d: 3 -> 
  e: noun -> T
d: 4 -> 
  e: nount -> T
d: 5 -> 
  e: atom -> |_
  e: cell -> [b [7 [f g]]] -> T
e: cell -> T
d: 6 ->
  e: atom -> |_
e: cell -> [b [6 [f g]]]
  f: noun -> T
g: atom -> |_
g: cell -> [b [6 [f [h i]]]]
  h: noun -> T
  i: noun -> T
d: 7 ->
  e: atom -> |_
  e: cell -> [b [7 [f g]]] -> T
d: 8 ->
  e: atom -> |_
  e: cell -> [b [8 [f g]]] -> T
d: 9 ->
  e: atom -> |_
  e: cell -> [b [9 [f g]]] -> T
d: 10 ->
  e: atom -> |_
  e: cell -> [b [10 [f g]]]
    g: noun -> T
  f: atom -> |_
     cell -> [b [10 [[h i] g]]]
    h: noun -> T
    i: noun -> T
d: 11 ->
  e: atom -> |_
  e: cell -> [b [11 [f g]]]
    g: noun -> T
  f: atom -> |_
     cell -> [b [11 [[h i] g]]]
    h: noun -> T
    i: noun -> T
d: 11 ->
  e: atom -> |_
  e: cell -> [b [11 [f g]]] -> T

|#

(define (raso i o)
  (fresh (a b c d e resa resb resc resd)
         (conde
          [ (atomo i) (== i o) ] ;single term, atomic
          [ (== `[,a ,b . ,c] i) 
            (== `(,d . ,e) c) (=/= '() e) ;complex c, more than three terms
	    (=/= 'nat d) ;do not capture an unenclosed nat
            (raso a resa) (raso b resb) (raso c resc) 
            (== `[,resa [,resb ,resc]] o) 
            ;(== `(a=,a b=,b c=,c d=,d e=,e resa=,resa resb=,resb resc=,resc) o)
            ]
          [ (== `[,a ,b . ,c] i) 
            (== `(,d . ()) c) ;simple c, three terms
	    (raso a resa) (raso b resb) (raso d resd)             
            (== `[,resa [,resb ,resd]] o) 
            ]
          [ (== `[,a ,b . ,c] i) 
            (== '() c) ;empty c, two terms
            (raso a resa) (raso b resb)
            (== `[,resa ,resb] o) ]
          )))

#|
TODO: cause reverse synthesis to converge during run*, and during complex reverse synthesis checks

racket@nocko> (run 1 (q) (raso q '[(nat 0) [(nat 0) (nat 0)]]))
'(((nat 0) (nat 0) (nat 0)))
racket@nocko> (run 2 (q) (raso q '[(nat 0) [(nat 0) (nat 0)]]))
'(((nat 0) (nat 0) (nat 0)) ((nat 0) ((nat 0) (nat 0))))
racket@nocko> (run 3 (q) (raso q '[(nat 0) [(nat 0) (nat 0)]]))
user break
racket@nocko> (run* (q) (raso q '[(nat 0) [(nat 0) (nat 0)]]))
user break
racket@nocko> 
|#

#|
`raso` constraint early to avoid divergence.
racket@nocko> (run 1 (p q) 
		   (cello q)
		   (raso p q)
		   (=/= p q))
user break
racket@nocko> (run 1 (p q) 
		   (raso p q)
		   (cello q)
		   (=/= p q))
'((((nat 0) (nat 0) (nat 0)) ((nat 0) ((nat 0) (nat 0)))))
racket@nocko> (run 1 (p q) 
		   (raso p q)
		   (=/= p q)
		   (cello q))
'((((nat 0) (nat 0) (nat 0)) ((nat 0) ((nat 0) (nat 0)))))
racket@nocko> (run 10 (p q) 
		   (raso p q)
		   (=/= p q)
		   (cello q))
'((((nat 0) (nat 0) (nat 0)) ((nat 0) ((nat 0) (nat 0))))
  (((nat 0) (nat 0) (nat 1)) ((nat 0) ((nat 0) (nat 1))))
  (((nat 0) (nat 1) (nat 0)) ((nat 0) ((nat 1) (nat 0))))
  (((nat 0) (nat 0) (nat 0 1)) ((nat 0) ((nat 0) (nat 0 1))))
  (((nat 0) (nat 0) (nat 1 1)) ((nat 0) ((nat 0) (nat 1 1))))
  (((nat 0) (nat 1) (nat 1)) ((nat 0) ((nat 1) (nat 1))))
  (((nat 0) (nat 0) (nat 0 0 1)) ((nat 0) ((nat 0) (nat 0 0 1))))
  (((nat 0) (nat 0) (nat 1 0 1)) ((nat 0) ((nat 0) (nat 1 0 1))))
  (((nat 0) (nat 1) (nat 0 1)) ((nat 0) ((nat 1) (nat 0 1))))
  (((nat 0) (nat 0) (nat 0 1 1)) ((nat 0) ((nat 0) (nat 0 1 1)))))
racket@nocko> 
|#

#|
(raso i)

i: atom -> T
i: [a b] ->
 a: atom -> T
 a: list -> T
|#


#|
(define (nevalo i o)
  (fresh (a b neg)
	 (noun a) (noun b)
	 (conde
	  [(== `(tar (,a ((nat 0) ,b))) i)
	   (== `(fas (,b ,a)) o)]
	  #;[(nexp i neg)
	   (=/= 't neg)]
	  ))
|#

#|
(define (nexp i o)
  (fresh (a b)
;	 (noun a) (noun b)
	 (conde
	  [(== `(tar (,a ((nat 0) ,b))) i)
	   (== 't o)])))   
|#

(define (npluso m n o) 
  (fresh (a b c)
	 (== `(nat . ,a) m) 
	 (== `(nat . ,b) n) 
	 (== `(nat . ,c) o) 
	 (conde
	  [(== '(0) a) (== '(0) b) (== '(0) c)]
	  [(== '(0) a) (=/= '(0) b) (pluso '() b c) (nato b)]
	  [(=/= '(0) a) (== '(0) b) (pluso a '() c) (nato a)]
	  [(=/= '(0) a) (=/= '(0) b) (pluso a b c) (nato a) (nato b)] 
          ;^nato constraints must follow pluso, else divergence.
	  )))

(define (nadd1o i o) (npluso i '(nat 1) o))

#|
(define (add1o i o)
  (fresh (num res)
	 (conde
	  [ (== '(nat 0) i) (== '(nat 1) o) ]
	  [ (== `(nat . ,num) i) (=/= '() num)
	    (== `(nat . ,res) o) 
	    (pluso num '(1) res) ] ;pluso call must be last, else run* diverges
	  )))
|#

;the nock operator `*`, meaning "evaluate", is pronouned "tar" (sTAR),
;which is used as the tag for `*` terms.

;[a b c] [a [b c]] 

;nock expressions are right associative. This redex suggests that, in
;addition to scanning the reduction rules from top to bottom, the nexp
;must be scanned from right to left. Given a non-fully delimited nexp
;[a1 a2 a3 ... ak], matching from left to right (comparable to
;outermost first reduction) to produce [a1 [a2 a3 ... ak]] requires a3
;... ak to already be understood as encompassed by `c` in the pattern
;[a b c]. However, if matched from right to left, [a1 ... ak-1 ak] can
;be parsed as [a1 ... [ak-1 ak]], with `c` matched to ak in terminal
;position. For both strategies, the recursive cases must be handled,
;whether of more than three terms at the same depth of the expression,
;or decomposition of any of terms a, b, or c into terms that must be
;auto-consed. The intent of a fully right-associated expression is
;conveyed by this line of the specification, but the mechanism is
;implementation dependent. If, for example, c is a deeply nested,
;non-fully right associated expression, e.g. [0 0 0 0], then there
;must be a way to focus on c, and perform an internal pattern match.


;autocons cannot match a term with four nouns, because it's pattern
;does not admit a list (of potentially arbitary size >=3), with the
;tail captured in the pattern variable `c`, but strictly an ordered
;tuple of three elements. Thus, an unparsed nock([a 6 b c d e]) -> *[a
;6 b c d e] -> *a -> LOOP. For autocons to group `d` and `e` within
;the cell `f`, the autocons window must intercept the six element
;tuple and check it from right to left, grouping as necessary.

;Kelvin versioning is an example of a finite critical developmental
;period in the lifecycle of a piece of software, with some precedent
;in Knuth's Pi versioning of TeX, which will similarly close its canon
;upon his death.
