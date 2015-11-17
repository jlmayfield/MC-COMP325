## TODO
##  --> write tests for eqC and lessC 
##  --> implement eq and less in the same style as the arithmetic
##  --> write up factorial examples as tests in check block
##      to explore further problems with letrec interpretation
##

data Binding:
  | bind(name :: String, value :: Value) 
end
type Environment = List<Binding>

data Value:
  | numV(n :: Number)
  | boolV(b :: Boolean)
  | closV(f :: ExprC%(is-fdC) , env :: Environment)
end

data ExprC:
    ## values
  | trueC
  | falseC
  | numC(n :: Number)    
  | fdC(param :: String, body :: ExprC)
    ## operators +, *, mulinv, ==, <
  | plusC(l :: ExprC, r :: ExprC)
  | multC(l :: ExprC, r :: ExprC)
  | mulinvC(e :: ExprC)
  | eqC(l :: ExprC, r :: ExprC)
  | lessC(l :: ExprC, r :: ExprC)
    ## Condtional, which covers and/or/not via short-circuit
  | ifC(i :: ExprC, t :: ExprC, e :: ExprC)
    ## functions, ids, and applicaitons
  | idC(id :: String)  
  | appC(f :: ExprC, arg :: ExprC)
    ## recursive local binding
  | letrecC(id :: String, val :: ExprC, body :: ExprC)
end

## Type checked boolean numeric operation
fun interp-arith(a :: ExprC, b :: ExprC, env :: Environment, f :: ( Number, Number -> Number)) -> Value:
  cases (Value) interp(a,env):
    | numV(l) =>     
      cases (Value) interp(b,env):
        | numV(r) => numV(f(l,r))
        | else => raise("interp: type error")
      end
    | else => raise("interp: type error")
  end
end

fun lookup(name :: String, env :: Environment) -> Value:
  cases (List) env:
    | empty => raise("free id " + name)
    | link(fst,rst) =>
      if fst.name == name:
        fst.value
      else:
        lookup(name,rst)
      end
  end
end

## Interperter 
fun interp(exp :: ExprC, env :: Environment) -> Value:
  cases (ExprC) exp: 
    | trueC => boolV(true)
    | falseC => boolV(false)
    | numC(n) => numV(n)    
      ## operators +, *, mulinv, ==, <
    | plusC(l, r) => interp-arith(l,r,env,lam(a,b): a + b;)
    | multC(l, r ) => interp-arith(l,r,env,lam(a,b): a * b;)
    | mulinvC(e) => 
      interp-arith(e,numC(1),env,
        lam(a,b):
          if a == 0 :
            raise("interp: Divide by zero error")
          else:
            1 / a
          end
        end)
    | eqC(l, r ) => numV(0)
    | lessC(l, r ) => numV(0)
    ## Condtional, which covers and/or/not via short-circuit
    | ifC(i , t , e ) => 
      ival = interp(i,env)
      cases (Value) ival:
        | boolV(shadow i) =>
          if i:
            interp(t,env)
          else:
            interp(e,env)
          end
      end    
      ## functions, ids, and applicaitons
    | fdC(f,a) => closV(fdC(f,a),env)
    | idC(name) => lookup(name,env)   
    | appC(f , arg ) => 
      thefun = interp(f,env)
      when not(is-closV(thefun)):
        raise("interp: expected function got something else")
      end
      
      # new code
      thebody = thefun.f.body
      
      # new identifier
      theparam = thefun.f.param
      thearg = interp(arg,env)
      
      #old environment
      thedefenv = thefun.env
      
      # GO!
      interp(thebody,link(bind(theparam,thearg),thedefenv))         
    | letrecC(i,v,b) => 
      def = interp(v,env)
      newclos = closV(def.f,link(bind(i,def),env))
      
      interp(b,link(bind(i,newclos),env))
  end 
where:
  interp(numC(5),empty) is numV(5)
  interp(trueC,empty) is boolV(true)
  interp(falseC,empty) is boolV(false)
  interp(fdC("x",numC(5)),empty) is
  closV(fdC("x",numC(5)),empty)
  
  interp(plusC(numC(5),trueC),empty) raises "type"
  interp(plusC(trueC,numC(5)),empty) raises "type"
  interp(plusC(numC(4),numC(5)),empty) is numV(9)
  
  interp(idC("x"),[list: bind("x",numV(7))]) is numV(7)
  interp(idC("x"),empty) raises "free"
  
  interp(appC(fdC("x",plusC(idC("x"),numC(5))),numC(7)),empty) is
  numV(12)
  
  #(((lam (y) (lam (x) (+ x y))) 5) 7)==> 12
  expr = 
    appC(
      appC(
        fdC("y",fdC("x",plusC(idC("x"),idC("y")))),
        numC(5)),numC(7))
  interp(expr,empty) is numV(12)
end


check "letrec":
  false is true
end



