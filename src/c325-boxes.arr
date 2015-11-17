import lists as L

## Environment maintains identifier scope
## and binds names to addresses. This effectively
## changes identifier semantics to implicit references
data Binding:
  | bind(id :: String, addr :: Number)
end
type Environment = List<Binding>

## The store is abstracted memory and binds
## addresses to values
data Storage:
  | cell(location :: Number, value :: Value)
end
type Store = List<Storage>

data Value:
  | numV(n :: Number)
  | closV(f :: ExprC%(is-fdC), env :: Environment)
  | boxV(l :: Number)
end

data ExprC:
    ## Some arithmetic
  | numC(n :: Number)  
  | plusC(l :: ExprC, r :: ExprC)
  | multC(l :: ExprC, r :: ExprC)
    ## First-Class Functions
    ## Also supports a basic let exp and let*
  | idC(id :: String)
  | fdC(param :: String, body :: ExprC)
  | appC(f :: ExprC , arg :: ExprC) 
    ## Boxes
  | boxC(v :: ExprC)
  | unboxC(b :: ExprC)
  | setboxC(b :: ExprC, v :: ExprC)
    ## Sequences
    ## n-steps --> 2 steps
  | seqC( fst :: ExprC, snd :: ExprC)
end

## find value bound to id in env or raise free id error
## if that id is unbound
fun lookup(id :: String, env :: Environment) -> Number:
  cases (List) env:
    | empty => raise("free id")
    | link(f,r) =>
      if f.id == id:        
        f.addr
      else:
        lookup(id,r)
      end
  end
where:
  lookup("n",empty) raises "free id"
  lookup("n",[list: bind("n",1)]) is 1
  lookup("x",[list: bind("n",1),bind("x",2)]) is 2
end  

## Get Value @ address addr from the Store sto
fun fetch(addr :: Number, sto :: Store) -> Value:
  cases (List) sto:
    | empty => raise("Address Not Found")
    | link(f,r) => 
      if f.location == addr:
        f.value
      else:
        fetch(addr,r)
      end
  end
where:
  fetch(1,empty) raises "Not Found"
  fetch(1,[list: cell(1,numV(2))]) is numV(2)
end

## adhoc constructor for the interpreter return values-> 
## the value of the interpreted expression and the 
## (potentially) modified store
fun ret(v :: Value, st :: Store):
  {v : v, st : st} 
where:
  ret(numV(0),empty).v is numV(0)
  ret(numV(0),empty).st is empty
  ret(numV(7),[list: cell(1,numV(5))]).v is numV(7)
  ret(numV(7),[list: cell(1,numV(5))]).st is [list: cell(1,numV(5))]
end

## Produces a zero-arg function that ticks
## through [1,...] 
fun addr-ticker():
  var addr = 1
  lam():
    next = addr
    addr := addr + 1
    next
  end
where:
  ne-loc = addr-ticker()
  ne-loc() is 1
  ne-loc() is 2
  ne-loc() is 3
  other-loc = addr-ticker()
  other-loc() is 1
  other-loc() is 2
  other-loc() is 3
end


## A No-Arg Constructor for an interpreter function with 
## locally encapsulated address allocator. It's 
## like an object with some private variables and
## methods. The only public method for the object
## is "interp" but we don't call it by name, we just
## "apply" the object. 
fun make-interp( ):# -> (ExprC, Environment, Store -> ):
  ## fresh address creator for this interp
  new-loc = addr-ticker()
  ## Dummy interp to solve circular dependency between
  ## interp and bin-num-op. Hey we used a variant of this
  ## paradigm for solving the letrec problem!
  var interp = lam(a,b,c): ret(numV(0),empty) end
  ## bin-num-op is now a private local function. 
  ## Hello information hiding and encapsulation
  bin-num-op =
    ## Typed checked numerical operator
    lam( l :: ExprC, r :: ExprC,
        env :: Environment, 
        sto :: Store , op):
      
      lhs = interp(l,env,sto)
      lval = lhs.v
      lsto = lhs.st  
      cases (Value) lval:
        | numV(shadow l) =>
          rhs = interp(r,env,lsto)
          rval = rhs.v
          rsto = rhs.st
          cases (Value) rhs.v:
            | numV(shadow r) => ret(numV(op(l,r)), rsto)          
            | else => raise("type error")
          end
        | else => raise("type error")
      end
    end
  ## Now that bin-num-op is declared and fully definied we can 
  ## set interp to the actual function
  interp :=
  lam(expr :: ExprC, env :: Environment, sto :: Store):
    cases (ExprC) expr:
      | numC(n)  => ret(numV(n),sto)
      | plusC(l,r) => bin-num-op(l,r,env,sto,lam(a,b): a + b;)
      | multC(l,r) => bin-num-op(l,r,env,sto,lam(a,b): a * b;)
        ## First-Class Functions
        ## Also supports a basic let exp and let*
      | idC(id) => 
        idaddr = lookup(id,env)
        idval = fetch(idaddr,sto)
        ret(idval,sto)
      | seqC(f,s) => 
        fst=interp(f,env,sto)
        interp(s,env,fst.st)      
      | fdC(_,_) => ret(closV(expr, env),sto)
      | boxC(v) => 
        ## interp value, allocate a cell for that value
        ## box now "points" to that cell
        val = interp(v, env, sto)
        loc = new-loc() ## new-loc must be in the environement
        ret(boxV(loc),link(cell(loc, val.v), val.st))      
      | unboxC(b) => 
        shadow b = interp(b,env,sto)
        bval = b.v
        bsto = b.st
        cases (Value) bval:
          | boxV(addr) => 
            ret(fetch(addr,bsto),bsto)
          | else => raise("can't unbox a non-box!")
        end        
      | setboxC(b,v) => 
        shadow b = interp(b,env,sto)
        cases (Value) b.v:
          | boxV(addr) =>
            shadow v = interp(v,env,b.st)
            ret(v.v, link(cell(b.v.l,v.v),b.st))           
          | else => raise("can't set a non-box")
        end               
      | appC(f,a) => 
        thefun = interp(f,env,sto)
        when not(is-closV(thefun.v)):
          raise("type error")
        end        
        aVal = interp(a,env, thefun.st )
        loc = new-loc()
        funEnv = link(bind(thefun.v.f.param, loc),thefun.v.env)
        funsto = link(cell(loc, aVal.v ) , aVal.st )
        interp(thefun.v.f.body,funEnv,funsto)                 
    end
  end
  ## return the now complete interp closure!
  ## [InterpDef with [new-loc, bin-num-op]]
  interp
where:
  ## No mutation so we can reuse this interp at will
   ## base cases
  make-interp()(numC(2),empty,empty) is ret(numV(2),empty)
  make-interp()(idC("n"),[list: bind("n",1)],[list: cell(1,numV(2))]) is 
  ret(numV(2),[list: cell(1,numV(2))])
  
  ## Alternatively you can construct a fresh interpreter 
  ##  and use the value directly
  make-interp()(plusC(numC(2),numC(4)),empty,empty) is ret(numV(6),empty)
  make-interp()(multC(numC(2),numC(4)),empty,empty) is ret(numV(8),empty)
  
  ## function defs
  make-interp()(fdC("n",idC("n")),empty,empty) is 
  ret(closV(fdC("n",idC("n")),empty),empty)
  
  ## Application
  make-interp()(appC(fdC("n",idC("n")),numC(2)),empty,empty) is 
  ret(numV(2),[list: cell(1,numV(2))])  
end

## Hide the initialization of environment and
## store within a function
fun run(expr :: ExprC):
  make-interp()(expr,empty,empty)
end

check "boxes":
  ## (box 4)
  make-interp()(boxC(numC(4)),empty,empty) is
  ret(boxV(1),[list: cell(1,numV(4))])
  
  make-interp()(boxC(numC(4)),empty,empty) is
  ret(boxV(1),[list: cell(1,numV(4))])  
  
  ## (unbox (box 4))
  make-interp()(unboxC(boxC(numC(4))),empty,empty) is
  ret(numV(4),[list: cell(1,numV(4))])
  
  ## (setbox (box 0) 5)
  ## Do we replace or do we push... push was the 
  ## environment strategy so we'll go with it... for now  
  make-interp()(setboxC(boxC(numC(0)),numC(5)),empty,empty) is
  ret(numV(5),[list: cell(1,numV(5)),cell(1,numV(0))])
  
  
  #|
     (let ([b (box 0)])
        (+ (begin 
              (set-box! b (+ 1 (unbox b)))
              (unbox b))
           (begin 
             (set-box! b (+ 1 (unbox b)))
             (unbox b))))
  |#
  
  #|
    (+ (let ([b (box 0)])
          1)
       b) 
  |#
  
    
  #|
    (let* ([a (box 1)]
           [f (fun x (+ x (unbox a)))])
       (begin
         (set-box! a 2)
         (f 10))) 
  |#  
  
end
