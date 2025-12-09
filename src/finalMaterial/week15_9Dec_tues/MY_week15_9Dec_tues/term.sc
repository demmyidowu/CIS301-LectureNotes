// #Sireum #Logika

import org.sireum._

def mult(x: Z, y: Z): Z = {
    Contract(
        Requires(y >= 0),
        Ensures(Res[Z] == x*y)
    )

    var sum: Z = 0
    var count: Z = 0

    //measure of work? (how many more iterations left?)
    //initially? y
    //after 1 iteration? y-1

    //in general? y - count

    while (count < y) {
        Invariant(
            Modifies(sum, count),
            count <= y,
            sum == x*count
        )

        //get measure of work: y - count

        sum = sum + x
        count = count + 1

        //get measure of work: y - count


        //measure should decrease with each iteration
            //does it? Yes since count increases with each iteration

        //when I have no work left, then my loop should be done
            //is it? y-count == 0 then y == count. Then loop condition is false
    }

    return sum
}

//We claim that multRec(x, y) will terminate for all non-negative y

//Base Case. multRec(x, 0) terminates, goes to base case (if statement) recursion not call

//Inductive step: Assume inductive hypothesis -- that multRec(x, k) terminates for some non
//negative integer k. We must prove that multRec(x, k+1) terminates. We know k+1 is at least 1, 
//so we would go into the else and make the recursive call multRec(x, k+1-1) which is multRec(x, k)
//which we know terminates by our inductive hypothesis. Thus multRec(x, k+1) will also terminate

def multRec(x: Z, y: Z): Z = {
    Contract(
        Requires(y >= 0),
        Ensures(Res[Z] == x*y)
    )

    var answer: Z = 0

    if (y == 0) {
        answer = 0
    } else {
        var temp: Z = mult(x, y-1)
        answer = x + temp
    }

    return answer
}

def collatz(n: Z): Z = {
    Contract(
        Requires(n > 0),
        Ensures(Res[Z] == 1)
    )

    //what if n is 52?
    //cur = ?

    var cur: Z = n
    while (cur > 1) {
        Invariant(
            Modifies(cur),
            cur >= 1        //what else could we say?
        )

        if (cur % 2 == 0) {
            cur = cur / 2
        } else {
            cur = 3 * cur + 1
        }
    }

    return cur
}