## Logan Mayfield
## A basic langauge for Arithmetic with binary
## +, *, and - and unary functions. Based off 
## PAPL chapter 15 section 1
## Functions with Arithmetic Expressions (FAE)

import s-exp as S
import lists as L

## Function Definition
data FunDefExt:
  | fdExt(name :: String, arg :: String, body ::  ExprExt)    
end
data FunDefC:
  | fdC(name :: String, arg :: String, body ::  ExprC)    
end

## Top level, user facing syntax representation
## for FAE Expressions
data ExprExt:
  | numExt(n :: Number)
  | idExt(i :: String)
  | plusExt(l :: ExprExt, r :: ExprExt)
  | multExt(l :: ExprExt, r :: ExprExt)
  | subExt(l :: ExprExt, r :: ExprExt)
  | appExt(name :: String , a :: ExprExt) 
end

## Type definition for FAE Core AST Type
##  This is the target value for the parser
data ExprC:
  | numC(n :: Number)
  | idC(i :: String)
  | plusC(l :: ExprC, r :: ExprC)
  | multC(l :: ExprC, r :: ExprC)
  | appC(name :: String, a :: ExprC )
end


## parse-fundef to map to defs
fun parse-def(d :: S.S-Exp) -> FunDefExt:
  ## This is what'd I'd call an abuse of short circuits
  ## It's bad style. I do it only as a demo of extremes.
  when
    (not(S.is-s-list(d))) or
    (d.exps.length() <> 3) or 
    (d.exps.get(0) <> S.s-sym("fun")) or 
    (not(S.is-s-list(d.exps.get(1)))) or
    (d.exps.get(1).exps.length() <> 2) or
    (L.any(lam(s): not(S.is-s-sym(s)) end , d.exps.get(1).exps)) or
    (d.exps.get(1).exps.get(0) == d.exps.get(1).exps.get(1)) :
    ## if one of the above fails, then the def wasn't syntactically correct
    raise("parse: Bad function definition")
  end
  ## If we made it this far, things are OK
  head = L.map(lam(sym): sym.s end, d.exps.get(1).exps)
  body = parse(d.exps.get(2))
  fdExt(head.first,head.rest.first,body)
where:
  fun pd(s :: String) -> FunDefExt:
    parse-def(S.read-s-exp(s))
  end
  
  pd("(fun (f a) 7)") is fdExt("f","a",numExt(7))
  pd("(foo (f a) 7)") raises "Bad"
  pd("(fun (f) 7)") raises "Bad"
  pd("(fun a 7)") raises "Bad"
  pd("(fun (f a b) 7)") raises "Bad"
  pd("(fun (f 5) 7)") raises "Bad"  
end

## Parser for simple FAE Extended Language
## fun parse(defs :: List<S.S-Exp>, src :: S.S-Exp)
fun parse(s :: S.S-Exp) -> ExprExt:
  cases (S.S-Exp) s:
    | s-num(n) => numExt(n)
    | s-list(shadow s) => parse-list(s)
    | s-sym(shadow s) => idExt(s)
    | s-str(shadow s) => raise("parse: expected arithmetic expresion. got " + s)    
  end
where:
  fun p(s): parse(S.read-s-exp(s)) end
  ## mult, plus, num
  p("(* (+ 1 2) (* 2 5))") is
  multExt(plusExt(numExt(1), numExt(2)), multExt(numExt(2), numExt(5)))  
  ## sub, num
  p("(- 4 5)") is
  subExt(numExt(4),numExt(5))
  ## identifiers
  p("dog") is idExt("dog")
  
  ## Error Cases
  p("(+ 4 ())") raises "expected arithmetic"
  p("(* 4 (+ dog \"cat\"))") raises "expected arithmetic"
end

## type/error check expression in operator position
## and return appropriate AST constructor or raise error
##   Return Type should be an ArithExt variant constructor
fun getopcons(s :: String) :
  if s == "+":
    plusExt
  else if s == "*":
    multExt
  else if s == "-":
    subExt
  else:
    raise("parse: unknown operator symbol/name")
  end
end

## parse-list is the helper for parse that parses the 
## list component of an s-list case
fun parse-list(l :: List<S.S-Exp>) -> ExprExt:
  cases (List) l:
    | empty => raise("parse: expected arithmetic expresion. got empty list")
    | link(op, args) =>
      when not(S.is-s-sym(op)):
        raise("parse: bad expression")
      end
      
      if args.length() == 2:
        argL = L.index(args, 0)
        argR = L.index(args, 1)
        getopcons(op.s)(parse(argL),parse(argR))
      else if args.length() == 1:
        appExt(op.s,parse(args.first))
      else:
        raise("parse: bad expression")
      end
  end
end


# Desugar the function definition.. well just the body of the function
# name and parameter name are left unchanged
fun desugar-def(def :: FunDefExt) -> FunDefC:
  cases (FunDefExt) def:
    | fdExt(n,a,b) =>
      fdC(n,a,desugar(b))
  end  
where:  
  desugar-def(fdExt("f","a",numExt(7))) is fdC("f","a",numC(7))
end

## translates user syntax trees to core langauge
## syntax trees
fun desugar(ast :: ExprExt) -> ExprC:
  cases (ExprExt) ast:
    | numExt(n) => numC(n)
    | idExt(s) => idC(s)
    | plusExt(l,r) => plusC(desugar(l),desugar(r))    
    | multExt(l,r) => multC(desugar(l),desugar(r))
    | subExt(l,r) => plusC(desugar(l),multC(numC(-1),desugar(r)))
    | appExt(n,a) => appC(n,desugar(a))
  end
where:
  ##(- 5 2) --> (+ 5 (* -1 2))
  desugar(subExt(numExt(5),numExt(2))) is
  plusC(numC(5),multC(numC(-1),numC(2)))
  desugar(plusExt(numExt(2),numExt(5))) is
  plusC(numC(2),numC(5))
  desugar(multExt(numExt(2),numExt(5))) is
  multC(numC(2),numC(5))
end



## interp is the core interpreter which evalutes an ArithC
## and converts it to an Number
fun interp(defs :: List<FunDefC> , src :: ExprC) -> Number:
  cases (ExprC) src:
    | numC(n) => n
      ## interp(progC(defs,l))
    | plusC(l,r) => interp(defs,l) + interp(defs,r) 
    | multC(l,r) => interp(defs,l) * interp(defs,r)
    | idC(s) => raise("Free Identifer")
    | appC(n,a) => 
      thefun = get-fundef(defs,n)
      interp(defs,subst(a,thefun.arg,thefun.body))      
  end      
where:
  interp(empty,numC(2)) is 2
  interp(empty,plusC(numC(2),numC(4))) is 6
  interp(empty,multC(numC(2),numC(4))) is 8
  interp(empty,multC(numC(7),plusC(numC(2),numC(4)))) is 42
  interp(empty,multC(plusC(numC(2),numC(4)),numC(7))) is 42
end

## Lookup he Definition of a function in the list of of definitions
fun get-fundef(defs :: List<FunDefC>, name :: String) -> FunDefC:
  cases (List) defs:
    | empty => raise(" I don't know what " + name + " is !")
    | link(f,r) => 
      if f.name == name:
        f
      else:
        get-fundef(r,name)
      end
  end
end

## replace all occurances of at in "in" with w
fun subst(w :: ExprC, at :: String, in :: ExprC) -> ExprC:
  cases (ExprC) in:
    | numC(_) => in
    | idC(s) =>
      if s == at:
        w
      else:
        in
      end
    | plusC(l,r) => plusC(subst(w,at,l),subst(w,at,r))
    | multC(l,r) => multC(subst(w,at,l),subst(w,at,r))
    | appC(n,a) =>  appC(n,subst(w,at,a))
  end
where:
  subst(numC(2), "n", idC("n")) is numC(2)
  subst(numC(2), "n" , multC(idC("n"),idC("n"))) is
  multC(numC(2),numC(2))
  subst(numC(2), "n", numC(5)) is numC(5)
  subst(numC(5), "x", plusC(idC("x"),idC("y"))) is
  plusC(numC(5),idC("y"))  
  subst(numC(5),"n",appC("n",numC(5))) is appC("n",numC(5))
  subst(numC(5),"n",appC("f",idC("n"))) is appC("f",numC(5))
end


## Programs are a list of functions, one of which should be named main
## this executes main
fun run(s :: String, n :: Number) -> Number:
  prog-sexp = S.read-s-exp(s)
  cases (S.S-Exp) prog-sexp:
    | s-list(defs) =>
      defsC = L.map(lam(d): desugar-def(parse-def(d)) end ,defs)
      interp(defsC,appC("main",numC(n)))      
    | else =>
      raise("Bad Program")      
  end  
where:
  run("((fun (main n) n))",5) is 5
  run("((fun (main n) (+ n 3)))",5) is 8
  run("((fun (f x) (* 5 x)) (fun (main n) (f n)))", 5) is 25
end
    


check "scope check":
  
  # if static
  run("( (fun (main x) (f 7)) (fun (f y) (* y x)))",2) raises "Free"
  
  # if dynamic
  #run("( (fun (main x) (f 7)) (fun (f y) (* y x)))",2) is 14
  
end

















