// #Sireum #Logika

//∀ ∃

import org.sireum._

//add 10 to all elements
def allPlus10(nums: ZS): Unit = {
  //function contract?
  Contract(
    Requires(), //Nothing to require
    Modifies(nums),
    Ensures(
      //describe how nums changs as a result if this function call
      ∀ (0 until nums.size) (k => nums(k) == In(nums)(k) + 10)
    )
  )

  var i: Z = 0
  while (i < nums.size) {
    //loop invariant block?
    Invariant(
      Modifies(i, nums),
      //Bound the loop counter
      i >= 0, i <= nums.size, 

      //Size of seq unchanged
      nums.size == In(nums).size,

      //Describe what has changed
      ∀ (0 until i) (k => nums(k) == In(nums)(k) + 10),

      //Describe what has NOT changed
      ∀ (i until nums.size) (k => nums(k) == In(nums)(k))
    )

    nums(i) = nums(i) + 10
    i = i + 1
  }
}

///////////////////////////

var test: ZS = ZS(4,1,3,8,10,2)

allPlus10(test)

//what do we want to assert?
assert(test == ZS(14, 11, 13, 18, 20, 12))