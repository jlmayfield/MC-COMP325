data Binding:
  | bind(name :: String, value :: Value) 
end
type Environment = List<Binding>

data Value:
  | numV(n :: Number)
  | boolV(b :: Boolean)
    # It would also work to make a recclosV with a ref env
    # and leave the closV as an immutable structure
  | closV(f :: ExprC%(is-fdC) , ref env :: Environment)       
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
  | letrecC(id :: String, val :: ExprC, body :: ExprC)
end


fun interp-binary(a :: ExprC, b :: ExprC, env :: Environment, 
    f , cons ) -> Value:
  cases (Value) interp(a,env):
    | numV(l) =>     
      cases (Value) interp(b,env):
          | numV(r) => cons(f(l,r))
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
    | plusC(l, r) => interp-binary(l,r,env,lam(a,b): a + b;,numV)
    | multC(l, r ) => interp-binary(l,r,env,lam(a,b): a * b;,numV)
    | mulinvC(e) => 
      interp-binary(e,numC(1),env,
        lam(a,b):
          if a == 0 :
            raise("interp: Divide by zero error")
          else:
            1 / a
          end
        end,
        numV)
    | eqC(l, r ) => interp-binary(l,r,env,lam(a,b): a == b;,boolV)
    | lessC(l, r ) => interp-binary(l,r,env,lam(a,b): a < b;,boolV)
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
      thedefenv = thefun!env         
      
      # GO!
      interp(thebody,link(bind(theparam,thearg),thedefenv))        
    | letrecC(i,v,b) =>  
      ## interpret the value... if it's a closure then we'll assume
      ##  it's recursive. otherwise no recursion can occur
      val = interp(v,env)
      cases (Value) val:
        | closV(_,ref _) =>           
          ## when the copy of val is made, a shallow copy of the ref is
          ## made, creating a circular environment. The instantiation
          ## of val allocated the space. The mutation can then use that 
          ## "address" to create the circular reference.          
          val!{env : link(bind(i,val),env)}
          ## at this point all we really need is val's environment
          ## that contains the circular reference to itself. This is a bit
          ## hacky in that if what we wanted was that environement,
          ## there there should be a design that gives us just that without
          ## the extra layer. For that we need a new, mutable
          ## data structure
          interp(b,val!env)
        | else =>
          interp(b,link(bind(i,val),env))
      end
  end     
where:
  interp(numC(5),empty) is numV(5)
  interp(trueC,empty) is boolV(true)
  interp(falseC,empty) is boolV(false)
  ## Refs mean we need a less hard-core sense of equality
  equal-now(interp(fdC("x",numC(5)),empty), closV(fdC("x",numC(5)),empty)) is true
  
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
  
  ## eq and less
  interp( eqC(numC(2),numC(2)) , empty) is boolV(true)
  interp( eqC(numC(3),numC(2)) , empty) is boolV(false)
  interp( eqC(trueC,numC(2)), empty) raises "type"
  interp( eqC(numC(2),falseC), empty) raises "type"
  interp( eqC(closV(fdC("n",idC("n")), empty),falseC), empty) raises "type"
  
  interp( lessC(numC(2),numC(2)) , empty) is boolV(false)
  interp( lessC(numC(3),numC(2)) , empty) is boolV(false)
  interp( lessC(numC(1),numC(2)) , empty) is boolV(true)
  interp( lessC(trueC,numC(2)), empty) raises "type"
  interp( lessC(numC(2),falseC), empty) raises "type"
  interp( lessC(closV(fdC("n",idC("n")), empty),falseC), empty) raises "type"
  
  
  ## Letrec
  facdef = fdC("n",ifC(eqC(idC("n"),numC(0)),numC(1),
      multC(idC("n"),appC(idC("fact"),plusC(numC(-1),idC("n"))))))
  facclos = closV(facdef,empty)
  facclos!{env : [list: bind("fact",facclos)]}
  ## Because we have refs involved we need to use equal-now. "is" uses
  ## a strong form of equals that fails to recognize the sameness of
  ## these items because the references are different.
  equal-now(interp(letrecC("fact",facdef,idC("fact")),empty),facclos) is true
  
end


check "recursive defs (i.e. letrec)":
  facdef = fdC("n",ifC(eqC(idC("n"),numC(0)),numC(1),
      multC(idC("n"),appC(idC("fact"),plusC(numC(-1),idC("n"))))))
  interp(letrecC("fact",facdef,appC(idC("fact"),numC(0))),empty) is numV(1)
  interp(letrecC("fact",facdef,appC(idC("fact"),numC(1))),empty) is numV(1)
  interp(letrecC("fact",facdef,appC(idC("fact"),numC(2))),empty) is numV(2)
  interp(letrecC("fact",facdef,appC(idC("fact"),numC(5))),empty) is numV(120)      
end
