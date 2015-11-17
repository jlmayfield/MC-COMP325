## Logan Mayfield
## A basic langauge for Arithmetic with binary
## + and * as described in PAPL Chapters 12 and 13.

import s-exp as S
import lists as L

## Type definition for Arithmetic Core AST Type
##  This is the target value for the parser
data ArithC:
  | numC(n :: Number)
  | plusC(l :: ArithC, r :: ArithC)
  | multC(l :: ArithC, r :: ArithC)
where:
  ## Variant Predicates/Constructors
  numC(5) satisfies is-numC
  is-numC( numC(5) ) is true #same as above
  plusC(numC(5),numC(4)) satisfies is-plusC
  multC(numC(5),numC(4)) satisfies is-multC
  ## Field Selection with dot (more Constructors)
  numC(5).n is 5
  plusC(numC(5),numC(4)).l is numC(5)
  plusC(numC(5),numC(4)).r is numC(4)
  multC(numC(5),numC(4)).l is numC(5)
  multC(numC(5),numC(4)).r is numC(4)
end


## Parser for simple Arithmetic Core Language
fun parse(s :: S.S-Exp) -> ArithC:
  cases (S.S-Exp) s:
    | s-num(n) => numC(n)
    | s-list(shadow s) => parse-list(s)
    | else => raise("parse: not number or list")
  end
where:
  fun p(s): parse(S.read-s-exp(s)) end
  ## One-shot all positive cases
  p("(* (+ 1 2) (* 2 5))") is
    multC(plusC(numC(1), numC(2)), multC(numC(2), numC(5)))  
  ## Error Cases
  p("(+ 4 ())") raises "unexpected empty list"
  p("(* 4 (+ dog \"cat\"))") raises "not number or list"  
end

## parse-list is the helper for parse that parses the 
## list component of an s-list case
fun parse-list(l :: List<S.S-Exp>) -> ArithC:
  cases (List) l:
    | empty => raise("parse: unexpected empty list")
    | link(op, args) =>
      var opcons = lam(lft,rht): raise("parse: Whoopsie") end
      if op.s == "+":
        opcons := lam(lft,rht): plusC(lft,rht) end
      else if op.s == "*":
        opcons := lam(lft,rht): multC(lft,rht) end
      else:
        raise("parse: invalid operator " + op.s)
      end     
      argL = L.index(args, 0)
      argR = L.index(args, 1)
      opcons(parse(argL),parse(argR))
  end
where:
  ## non-error cases
  parse-list([list: S.s-sym("+"), S.s-num(3), S.s-num(5)]) is
  plusC(numC(3),numC(5))
  parse-list([list: S.s-sym("*"), S.s-num(3), S.s-num(5)]) is
  multC(numC(3),numC(5))
  
  ## Error cases
  parse-list([list: S.s-sym("+"),
      S.s-num(4),S.s-list(empty)]) raises "unexpected empty list"
end
























