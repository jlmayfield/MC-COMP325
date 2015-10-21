
## Reduced Extended Language
##  - andExt should desugar to conditionals that carry out short-circuit semantics
##  - condExt should desugar to to nested ifCs
data ExprExt:
  | trueExt
  | falseExt
  | idExt(id :: String)
  | appExt(name :: String, args :: List<ExprExt>)
  | andExt(rands :: List<ExprExt>)
    ## Note on CondExt:
    ## the clauses list is at least length 2 with the first
    ## of type ifthenClause and the second an elseClause.
    ## for length > 2, the first length-1 are ifThenClauses and
    ## the last is an elseClause.  This precondition is
    ## guaranteed by the parser
  | condExt(clauses :: List<condClause>)
  | ifExt(i :: ExprExt, t :: ExprExt, e :: ExprExt)   
end

## The pieces of a Conditional expression
data condClause:    
  | ifthenClause(i :: ExprExt, t :: ExprExt)
  | elseClause(e :: ExprExt)
end

## Reduced Core Language
data ExprC:
  | trueC
  | falseC
  | idC(id :: String)
  | appC(name :: String, args :: List<ExprC>)    
  | ifExt(i :: ExprExt, t :: ExprExt, e :: ExprExt)       
end

## Function Definitions
data FunDefExt:
  | fdExt(name :: String, args :: List<Strings>, body :: ExprExt)    
end
data FunDefC:
  | fdExt(name :: String, args :: List<Strings>, body :: ExprC)    
end