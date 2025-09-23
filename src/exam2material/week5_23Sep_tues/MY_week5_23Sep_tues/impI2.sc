// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def imply2(p: B, q: B, r: B): Unit = {
  Deduce(
    (p __>: r, q __>: r ) |- ( p | q __>: r  )
      Proof(
      1 (  p __>: r   ) by Premise,
      2 (  q __>: r   ) by Premise,
      3 SubProof(
        4 Assume ( p | q ),
        5 SubProof(
          6 Assume ( p ),
          7 
        )
        
      )

    )
  )
}