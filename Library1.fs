namespace Library1
open System
open System.Numerics
module main=
    let divisorList=[1;2;3;4;6;8;12;24]
    //let test=divisorList|>List.map(fun x->(divTest.maxDivisorContribution (1L,0L) x)/x)//|>List.sum
    //printf "testAns=%A\n\r" test
    let findSum y=divisorList|>List.map(fun x->divTest.maxDivisorContribution y x)|>List.fold(fun acc x->divTest.mod109 (acc+x)) 0L
    let fibSeq=Seq.unfold(fun (prev,prevprev,n)->
        let nextFib=divTest.stateAdd prev prevprev
        if(n<123456L) then Some (prev ,(nextFib,prev,n+1L))
        else None) (divTest.initState1,divTest.initState2,1L)
    //Seq.iter(fun x->printf "%A\n\r" x)fibSeq
    printf "testAns%A\n\r" (findSum (10000L/24L,int (10000L%24L)))
    //let finalAns=Seq.map(fun x->findSum x) fibSeq
    let finalAns=Seq.fold(fun acc x->divTest.mod109 (acc+findSum x)) 0L fibSeq
    //Seq.iter(fun x->printf "%A\n\r" x ) finalAns
    printf "%A" finalAns
    //let testIntermediate=divTest.maxDivisorTripletMap.[4]
    //let dummy=Seq.iter(fun x->printf "%A\n\r"x ) testIntermediate
    //printf "test=%A" test10
    System.Console.ReadLine()|>ignore 