namespace Library1
open System
open System.Numerics
module main=
    let divisorList=[1;2;3;4;6;8;12;24]
    //let test=divisorList|>List.map(fun x->(divTest.maxDivisorContribution (1L,0L) x)/x)//|>List.sum
    //printf "testAns=%A\n\r" test
    let N=1502L
    
    //Seq.iter(fun x->printf "%A\n\r" x)fibSeq
    let createState N=
        let q=N/24L
        let r=N%24L
        match r with
        |0L->(q-1L,24)
        |_->(q,int r)
    printf "testAns%A\n\r" (divTest.findSum2 (createState 10L))
    printf "newFibSumAns%A\n\r" (divTest.fibSum 9 N)
    printfn "%A" (List.init 20 (fun i->divTest.FibFromPhiModK 10000I (BigInteger i)))
    //let finalAns=Seq.map(fun x->findSum x) fibSeq
    //let finalAns=Seq.fold(fun acc x->divTest.mod109 (acc+divTest.findSum2 x)) 0L fibSeq
    //Seq.iter(fun x->printf "%A\n\r" x ) finalAns
    //printf "%A" finalAns
    //let testIntermediate=divTest.maxDivisorTripletMap.[4]
    //let dummy=Seq.iter(fun x->printf "%A\n\r"x ) testIntermediate
    //printf "test=%A" test10
    System.Console.ReadLine()|>ignore 