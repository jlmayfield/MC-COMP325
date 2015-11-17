import s-exp as S


## Some Unit tests that demo read-s-exp
check "good sexpressions":
  
  ## some base case tests
  S.read-s-exp("5") is S.s-num(5)
  S.read-s-exp("\"hello\"") is S.s-str("hello")
  S.read-s-exp("anid") is S.s-sym("anid")
  
  ## lists
  S.read-s-exp("()") is S.s-list(empty)
  S.read-s-exp("((\"this\") 7 hi)") is
  S.s-list([list: S.s-list([list: S.s-str("this")]),
      S.s-num(7),S.s-sym("hi")])
end

## Error tests for S.read-s-exp
check "bad sexpressions":
  S.read-s-exp("(5") raises "Invalid s-expression"
  
  ## Frankly, I'm not sure how to catch this error message so 
  ## I'm just punting to "" to catch any error. This kind of 
  ## vagueness is bad though. Avoid it whenever possible
  S.read-s-exp(5) raises ""
end
