## Logan Mayfield 
### High-Ordered versions of classic functions

import lists as L

## mymap : (f :: ( a -> b )) -> (List<a> -> List<b>)
##   Construct the map  that computes the list of bs that results
##   from applying f to each element of lst
fun mymap<a,b>( f :: ( a-> b ) ) ->  (List<a> -> List<b>):
  lam(l :: List<a>) -> List<b>: 
    cases (List) l:
      | empty => empty        
      | link(fst,rst) =>  
        link( f(fst), mymap(f)(rst) )        
    end
  end
where:
  ## "zero out" the list
  mapzero = mymap(lam(n): 0;) ## name the function
  mapzero(empty) is empty
  mapzero([list: 1, 2, 3]) is [list: 0, 0, 0]
  
  ## get the lengths of a list of lists
  mymap(lam(l):l.length();)([list: empty, [list: 1,2], [list: 1,2,3,4,5,6]]) is
  [list: 0,2,6]  
end

## myfold : (f :: (c a -> c), init :: c , lst :: List<a> -> c)
##   Construct the c that results from iteratively applying
##   f to each element of lst in left to right order 
##   finishing with init 
##   
fun myfold<a,c>( f :: (c,a -> c), init :: c) -> (List<a> -> c):
  lam(lst :: List<a>) -> c:
    cases (List) lst:
      | empty => init
      | link(fst,rst) =>
        f( myfold(f,init)(rst),  fst ) 
    end
  end
where:
  sumnums = myfold(lam(acc,n): n + acc;, 0)
  sumnums(empty) is 0
  sumnums([list: 1, 2, 3]) is 6
  
  maptolength = myfold(lam(acc,l): link(l.length(),acc);,empty)
  maptolength(empty) is empty
  maptolength([list: empty, [list: 1,2], [list: 1,2,3,4]]) is
  [list: 0,2,4]
  
  getevens = myfold(
    lam(acc,n): 
      if num-modulo(n,2) == 0:
        link(n,acc)
      else:
        acc
      end
    end,
    empty)
  
  getevens(empty) is empty
  getevens([list: 1,3,5]) is empty
  getevens([list: 1,2,3,4,5]) is [list: 2,4]
end
    

## myfilter:  (f :: (a -> Boolean), lst :: List<a> -> List<a>)
##   Select all the elements from lst for which f holds
fun myfilter<a>(f :: (a -> Boolean) ) -> (List<a> -> List<a>):
  lam(lst :: List<a>) -> List<a>:
    cases (List) lst:
      | empty => empty
      | link(fst,rst) =>   
        if f(fst):
          link(fst,myfilter(f)(rst))
        else:
          myfilter(f)(rst)
        end
    end
  end 
where:
  fun iseven(n): num-modulo(n,2) == 0 end
  getevens = myfilter(iseven)
  
  getevens(empty) is empty
  getevens([list: 1,3,5]) is empty
  getevens([list: 1,2,3,4,5]) is [list: 2,4]
  
end

## myandmap : (f :: (a -> Boolean), lst :: List<a> -> Boolean)
##  True if f holds for all elements of lst

## myormap : (f :: (a -> Boolean), lst :: List<a> -> Boolean)
##   True if f holds for at least one element of lst


















