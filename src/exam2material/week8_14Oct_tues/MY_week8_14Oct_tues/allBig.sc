// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._



@pure def allBig[T](P: T=>B @pure, Q: T=>B @pure, R: T=>B @pure, B: T=>B @pure, C: T=>B @pure): Unit = {
  Deduce(
    (
        ∀((x: T) => (P(x) __>: B(x)  )),
        ∀((x: T) => (Q(x) __>: C(x)  )),
        ∀((x: T) => (R(x) __>: !B(x) & !C(x)  ))
    )
      |-
    (
      ∀((x: T) => (P(x) | Q(x) __>: !R(x)  ))
    )
    Proof(
      1 ( ∀((x: T) => (P(x) __>: B(x)  )) ) by Premise,
      2 ( ∀((x: T) => (Q(x) __>: C(x)  )) ) by Premise,
      3 ( ∀((x: T) => (R(x) __>: !B(x) & !C(x)  )) ) by Premise,
      4 Let ((a: T) => SubProof(
        6 SubProof(
          7 Assume ( P(a) | Q(a) ),
          8 ( P(a) __>: B(a) ) by AllE[T](1),
          9 ( Q(a) __>: C(a) ) by AllE[T](2),
          10 ( R(a) __>: !B(a) & !C(a) ) by AllE[T](3),
          11 SubProof(
            12 Assume ( R(a) ),
            13 ( !B(a) & !C(a) ) by ImplyE(10, 12),
            14 ( !B(a) ) by AndE1(13),
            15 ( !C(a) ) by AndE2(13),
            16 SubProof(
              17 Assume ( P(a) ),
              18 ( B(a) ) by ImplyE(8, 17),
              19 ( F ) by NegE(18, 14)
            ),
            20 SubProof(
              21 Assume( Q(a) ),
              22 ( C(a) ) by ImplyE(9, 21),
              23 ( F ) by NegE(22, 15) 
            ),
            24 ( F ) by OrE(7, 16, 20)
          ),
          25 ( !R(a) ) by NegI(11)
        ),
        26 ( P(a) | Q(a) __>: !R(a) ) by ImplyI(6)
      )),
      27 ( ∀((x: T) => (P(x) | Q(x) __>: !R(x))) ) by AllI[T](4)
      
    )
  )
}