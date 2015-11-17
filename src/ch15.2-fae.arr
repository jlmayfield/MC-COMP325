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

## An identifier to Value binding
data Binding:
  | bind(name :: String, value :: Number)
end

## Renaming of types/functions for 
## Environment Logic
type Environment = List<Binding>
mt-env = empty
xtnd-env = link


## parse-fundef 
fun parse-def(def :: S.S-Exp) -> FunDefExt:
  cases (S.S-Exp) def:
    | s-list(l) => 
      ask:
        | l.length() <> 3 then:
          raise("Bad Function Definition")
        | ( index(l,0) <> S.s-sym("fun") ) or 
          ( not(S.is-s-list(index(l,1)) ) and 
            ( ((index(l,1)).exps).length() == 2 ) )
          then:
          raise("Bad Function Definition")
        | otherwise:
          ### assuming well-formed def at this point... 
          nm = index(index(l,1).exps,0).s ## name
          ag = index(index(l,1).exps,1).s ## arg name
          bd = index(l,2)
          fdExt(nm,ag,parse-expr(bd))
      end     
    | else =>
      raise("Bad Function Definition")
  end
  
where:
  fun p(s): parse-def(S.read-s-exp(s)) end
  
  p("(fun (f x) 5)") is fdExt("f","x",numExt(5))
end

## Parser for simple FAE Extended Language
## fun parse(defs :: List<S.S-Exp>, src :: S.S-Exp)
fun parse-expr(s :: S.S-Exp) -> ExprExt:
  cases (S.S-Exp) s:
    | s-num(n) => numExt(n)
    | s-list(shadow s) => parse-list(s)    
    | s-sym(shadow s) => idExt(s)
    | s-str(shadow s) => raise("parse: expected arithmetic expresion. got " + s)
  end
where:
  fun p(s): parse-expr(S.read-s-exp(s)) end
  ## mult, plus, num
  p("(* (+ 1 2) (* 2 5))") is
  multExt(plusExt(numExt(1), numExt(2)), multExt(numExt(2), numExt(5)))  
  ## sub, num
  p("(- 4 5)") is
  subExt(numExt(4),numExt(5))
  p("dog") is idExt("dog")
  
  ## Error Cases
  p("(+ 4 ())") raises "expected arithmetic"
  ## cat is the problem here
  p("(* 4 (+ dog \"cat\"))") raises "expected arithmetic"
end

## type/error check expression in operator position
## and return appropriate AST constructor or raise error
##   Return Type should be an ArithExt variant constructor
fun getopcons(op :: S.S-Exp):
  cases (S.S-Exp) op:
    | s-sym(s) =>
      if s == "+":
        plusExt
      else if s == "*":
        multExt
      else if s == "-":
        subExt
      else:
        raise("parse: unknown operator symbol/name")
      end
    | else => raise("parse: expecting operator symbol/name. didn't get it")      
  end
end

## parse-list is the helper for parse that parses the 
## list component of an s-list case
fun parse-list(l :: List<S.S-Exp>) -> ExprExt:
  cases (List) l:
    | empty => raise("parse: expected arithmetic expresion. got empty list")
    | link(op, args) =>
      ask:
        | args.length() == 2 then:
          argL = L.index(args, 0)
          argR = L.index(args, 1)
          getopcons(op)(parse-expr(argL),parse-expr(argR))
        | args.length() == 1 then:
          fname = op.s
          farg = L.index(args,0)
          appExt(fname,parse-expr(farg))
        | otherwise:
          raise("Bad Expression")
      end
  end
end

## Desugar a FunDefExt to the Core equivalent
fun desugar-def(def :: FunDefExt) -> FunDefC:
  cases (FunDefExt) def:
    | fdExt(n,a,b) => fdC(n,a,desugar-expr(b)) 
  end
where:
  desugar-def(fdExt("f","x",numExt(0))) is fdC("f","x",numC(0))
end

## translates user syntax trees to core langauge
## syntax trees
fun desugar-expr(ast :: ExprExt) -> ExprC:
  cases (ExprExt) ast:
    | numExt(n) => numC(n)
    | plusExt(l,r) => plusC(desugar-expr(l),desugar-expr(r))    
    | multExt(l,r) => multC(desugar-expr(l),desugar-expr(r))
    | subExt(l,r) => plusC(desugar-expr(l),multC(numC(-1),desugar-expr(r)))
    | idExt(s) => idC(s)
    | appExt(n,a) => appC(n,desugar-expr(a))
  end
where:
  ##(- 5 2) --> (+ 5 (* -1 2))
  desugar-expr(subExt(numExt(5),numExt(2))) is
  plusC(numC(5),multC(numC(-1),numC(2)))
  desugar-expr(plusExt(numExt(2),numExt(5))) is
  plusC(numC(2),numC(5))
  desugar-expr(multExt(numExt(2),numExt(5))) is
  multC(numC(2),numC(5))
end

fun lookup-id(id :: String, env :: Environment) -> Number:
  cases (Environment) env:
    | empty => raise("Free identifier " + id)
    | link(f,r) => 
      cases (Binding) f:
        | bind(n,v) =>
          ask:
            | n == id then:
              v
            | otherwise:
              lookup-id(id,r)
          end
      end
  end
where:
  lookup-id("n",xtnd-env(bind("n",5),mt-env)) is 5
end

## interp is the core interpreter which evalutes an ArithC
## and converts it to an Number
fun interp(defs:: List<FunDefC>, ast :: ExprC, env :: Environment) -> Number:
  cases (ExprC) ast:
    | numC(n) => n      
    | plusC(l,r) => interp(defs,l,env) + interp(defs,r,env) 
    | multC(l,r) => interp(defs,l,env) * interp(defs,r,env)
    | idC(s) => lookup-id(s,env)
    | appC(n,a) => 
      thefun = get-fundef(defs,n)
      thearg = interp(defs,a,env)
      new-env = xtnd-env(bind(thefun.arg,thearg), mt-env)
      
      interp(defs,thefun.body, new-env)
  end      
where:
  interp(empty,numC(2),mt-env) is 2
  interp(empty,plusC(numC(2),numC(4)),mt-env) is 6
  interp(empty,multC(numC(2),numC(4)),mt-env) is 8
  interp(empty,multC(numC(7),plusC(numC(2),numC(4))),mt-env) is 42
  interp(empty,multC(plusC(numC(2),numC(4)),numC(7)),mt-env) is 42
end

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


fun run-program(defs :: String,src :: String) -> Number:
  shadow defs = S.read-s-exp(defs)
  cases (S.S-Exp) defs:
    | s-list(shadow defs) =>
      ## read code src
      shadow src = S.read-s-exp(src)
      ## parse+desug for a function definition
      prepdfs = lam(d): desugar-def(parse-def(d)) end
      interp(
        ## process the defs down to Core Defs
        L.map(prepdfs,defs),
        ## process the src down to core
        desugar-expr(parse-expr(src)),
        mt-env
        )
    | else =>
      raise(" Bad Def list")
  end  
where:
  run-program("()","5") is 5
  run-program("()","(- 3 (* 5 2))") is -7  
  
  ## functions
  run-program("((fun (sq x) (* x x)))","(sq 3)") is 9
  run-program("((fun (sq x) (* x x)) (fun (quad y) (* (sq y) (sq y))))","(quad 3)") is 81
end


check "static scope tests":
  ## raw free ID
  run-program("((fun (f x) (+ x y)))","(f 5)") raises "Free"
  
  ## Static Scope check
  run-program("((fun (f x) (+ x y)) (fun (g y) (f 5)))","(g 6)") raises "Free"
end


    




















