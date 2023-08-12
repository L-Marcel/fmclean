namespace Samples

#eval 2+2

def sampleFunction1(x) := 
  x*x + x + 3

def result1 := sampleFunction1 4573

#eval "The result of squaring the integer 4573 and adding 3 is " ++ to_string result1

def sampleFunction2(x y) := 
  2*x*x - x + 3 + y

def result2 := 
  sampleFunction2 (7 + 4) 8

#eval "The result of applying the 2nd sample function to (7 + 4) is " ++ to_string result2

def sampleFunction3(x) :=
  if x > 100 then
    2*x*x - x + 3
  else
    2*x*x + x - 37

#eval "The result of applying sampleFunction3 to 2 is " ++ to_string (sampleFunction3 2)

end Samples