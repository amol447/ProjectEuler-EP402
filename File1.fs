module divTest

open System
open System.Numerics
open System.Collections.Generic
open FsCheck
type listMonadBuilder()=
        member x.Bind(comp,func)= comp|>List.map(fun x->func x)|> List.concat
        member x.Return(comp)=[comp]
let mod2Test a b c= 0=((1+a+b+c) % 2)
let mod3Test a b c= (2=b%3) && (0=(a+c)%3)
let mod4Test a b c=
    match a%4 with
    |x when ((x=0)||(x=2))->( 0=( (a+c)%4) && (3=b%4) )   ||( (2=(a+c)%4)&&(1=b%4) )
    |_->false 
let mod8Test a b c=
    match (a%8,b%8,c%8) with
    |x when x=(6,3,6)->true
    |x when x=(2,7,6)->true
    |x when x=(2,3,2)->true
    |x when x=(6,7,2)->true 
    |_->false
let modnTest n a b c=
    match n with
    |1->true
    |2->mod2Test a b c
    |3->mod3Test a b c
    |4->mod4Test a b c
    |6->(mod2Test a b c) && (mod3Test a b c)
    |8->mod8Test a b c
    |12->(mod4Test a b c) && (mod3Test a b c)
    |24->(mod8Test a b c)&& (mod3Test a b  c)
    |_->false
let poly x  a b c = (pown x 4) + (pown x 3)*a+(pown x 2)*b+x*c
//let polyDivTest x a b c n= 0=(poly x a b c) % n
let xor a b=(a&& not b)||(b&& not a)
(*let modnTestTest n a b c=
    let actualAns=[1..100]|>List.forall(fun x->polyDivTest x a b c n)
    let testAns=modnTest n (int64 a) (int64 b) (int64 c)
    not (xor actualAns  testAns)*)
let fibInc (F1,F2)=(F2,F2+F1)
let inline boolToInt b=
    match b with
    |true->int64 1
    |_->int64 0
//let countIMod24TilM (m:int64)  (i:int64)=
//    match m%(24) with
//    |x when x>=i->1L+m/24- (boolToInt (i=0))
//    |_->m/24-(boolToInt (i=0))



let abcTriplets=
    listMonadBuilder(){
        let!x=[0..23]
        let!y=[0..23]
        let!z=[0..23]
        return x,y,z}
let findMaxDivisor  y=
    let powersOf2 x=Seq.unfold(fun state->match (x|||>modnTest state ) with
                                              |true->Some(state,2*state)
                                              |false->None) 1
                        |>Seq.last
    let test3=match (y|||>modnTest 3)  with
              |true->3
              |false->1
    test3*powersOf2 y
//let a=findMaxDivisor (3,4,5L)
let maxDivisorTriplet=abcTriplets|>List.map(fun x->findMaxDivisor x)
let maxDivisorTripletMap=maxDivisorTriplet|>Seq.zip abcTriplets|>Seq.groupBy(fun (x,y)->y)|>Map.ofSeq|>Map.map(fun key value->Seq.map(fun x->fst x) value)
//let testMap n=maxDivisorTripletMap|>Map.map(fun key value->Seq.filter(fun (a,b,c)->(a<=n) && (b<=n) && (c<=n) && (a > 0L) && (b>0L) && (c>0L))  value)
                                  //|>Map.map(fun key value->Seq.length value)
                                  //|>Map.fold(fun acc key value->acc+key*value) 0
let inline mod109 x= x%(pown 10L 9)
let initState1=(0L,1)
let initState2=(0L,1)
               
let stateAdd (q1,r1) (q2,r2) = 
    let remTemp=(r1+r2)
    let rem=match remTemp with
            |x when x>23->((x-24),true)
            |_->(remTemp,false)
    let quotient = (q1+q2+(boolToInt (snd rem)))|>mod109
    (quotient,fst rem)
//let dictIModN =
//let countNumTripletsPartial  state=
//    let numRemainderArray=Array.init 24 (fun x->match x with 
//                                                |y when y<=snd state->1L-(boolToInt (int64 y=0L) ) + fst state
//                                                |_->fst state)
//    (fun (x,y,z)-> (numRemainderArray.[x]*numRemainderArray.[ y]) |>mod109|>(fun x ->x*numRemainderArray.[z])|>mod109)
let numRemainderFunc state x= 
        match x with
        |y when y=0->fst state
        |y when y<=snd state->1L+fst state      
        |_->fst state  
//let countNumTriplets (a,b,c) state= (countNumTripletsPartial state )(a,b,c)
let maxDivisorContribution state d  =
    let numRemainderMap= numRemainderFunc state
    maxDivisorTripletMap.[d]|>Seq.map(fun (a,b,c)->(numRemainderMap a)*numRemainderMap b|>mod109|>(fun x->x*numRemainderMap c)|>mod109)
    |>Seq.fold(fun acc x->mod109 (acc+x)) 0L 
    |>(fun x-> x *int64 d)|>mod109

