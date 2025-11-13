// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//want to return x * y, through repeated addition
//recursively compute x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //what goes here?
  //what should we require?
  //what should we ensure?
  Contract(
    Requires( y >= 0 ),
    Ensures( Res[Z] == x * y )
  )

  var answer: Z = 0

  if (y == 0) {
    answer = 0
    
    //what do we need to do here?
    Deduce(
      1 ( y == 0 ) by Premise,
      2 ( answer == 0 ) by Premise,
      3 ( answer == x * y ) by Algebra*(1, 2)
    )
  } else {
    
    Deduce(
      1 ( !(y == 0) ) by Premise,
      2 ( y != 0 ) by Algebra*(1),
      3 ( y >= 0 ) by Premise,
      4 ( (y-1) >= 0 ) by Algebra*(2, 3)
    )
    //return x * (y-1)
    var temp: Z = mult(x, y-1)
    answer = x + temp

    //what do we need to show here?
    Deduce(
      1 ( !(y == 0) ) by Premise,
      2 ( temp == x * (y - 1) ) by Premise,
      3 ( answer == x + temp ) by Premise,
      4 ( answer == x * y ) by Algebra*(2, 3)
    )

  }

  //what do we need to do here?
  Deduce(
    1 ( answer == x * y ) by Premise
  )
  return answer
}

////////////// Test code //////////////

val a: Z = 5
val b: Z = 4

Deduce(
  1 ( b == 4 ) by Premise,
  2 ( b >= 0 ) by Algebra*(1)
)

var ans: Z = mult(a, b)

Deduce(
  1 ( a == 5 ) by Premise,
  2 ( b == 4 ) by Premise,
  3 ( ans == a * b ) by Premise,
  4 ( ans == 20 ) by Algebra*(1, 2, 3)
)

//what do we want to assert that ans is?
assert(ans == 20)