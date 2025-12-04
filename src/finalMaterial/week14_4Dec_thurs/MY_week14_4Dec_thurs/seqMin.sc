// #Sireum #Logika

//∀ ∃

import org.sireum._

//return the smallest element in list
def min(list: ZS): Z = {
    //contract?
    Contract(
        Requires(list.size >= 1),
        Ensures(
            //Describe the return value
            //<= all elements in the seq and there's an element in seq equal to it
            ∀ (0 until list.size) (k => Res[Z] <= list(k)),
            ∃ (0 until list.size) (k => list(k) == Res[Z])
        )
    )

    var small: Z = list(0)
    var i: Z = 1
    
    while (i < list.size) {
        //invariant?
        Invariant(
            Modifies(i, small),
            i >= 1, i <= list.size,
            ∀ (0 until i) (k => small <= list(k)),
            ∃ (0 until i) (k => list(k) == small)
        )

        if (list(i) < small) {
            small = list(i)
        }
        i = i + 1
    }

    return small
}

////////////// Calling code ///////////////////

var test: ZS = ZS(8,1,0,10,9,2,0)
var testMin: Z = min(test)

//what should testMin be?
assert(testMin == 0)