predicate isSol(sol : seq<int>, nr:int)
   requires |sol| == 3
   requires sol[0]>=0
   requires sol[1]>=0
   requires sol[2]>=0
{
    sol[0]*1+sol[1]*5+sol[2]*10 == nr

}

function cost(sol : seq<int>):int 
   requires |sol| == 3
   requires sol[0]>=0
   requires sol[1]>=0
   requires sol[2]>=0
{
    sol[0]+sol[1]+sol[2]
}

predicate isOptSol(sol : seq<int>, nr:int)
    requires |sol| == 3
    requires sol[0]>=0
    requires sol[1]>=0
    requires sol[2]>=0
{   
  isSol(sol,nr) &&
  forall sol' :: |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0 && isSol(sol',nr) 
          ==> cost(sol') >= cost(sol)

}

predicate INV(copie: int, nr: int, s1: int, s5: int, s10:int)
  requires s1 >= 0
  requires s5 >= 0
  requires s10 >= 0
{
   forall s1', s5', s10' :: s1'>=0 && s5'>=0 && s10'>=0 ==>
          (isSol([s1',s5',s10'],copie) ==> 
          isSol([s1+s1',s5+s5',s10+s10'],nr)) &&
          (isOptSol([s1',s5',s10'],copie) ==> 
          isOptSol([s1+s1',s5+s5',s10+s10'],nr))
}


method findMax(nr: int) returns(s:int)
  requires nr > 0
  ensures 0 < s <= nr
  ensures s == 1 || s == 5 || s == 10
  ensures s == 1 ==> nr < 5
  ensures s == 5 ==> nr >= 5
  ensures s == 10 ==> nr >= 10
  
{
  if(nr >= 10){
    s := 10;
  }
  if(nr >= 5){
    s := 5;
  }
  if(nr < 5){
    s := 1; 
  }
  
}


lemma caz1(copie: int, nr: int, s1: int, s5: int, s10: int)
  requires copie < 5
  requires s1 >= 0
  requires s5 >= 0
  requires s10 >= 0
  requires INV(copie,nr,s1,s5,s10)
  ensures INV(copie-1,nr,s1+1,s5,s10)
{

  forall s1', s5', s10' | s1'>=0 && s5'>=0 && s10'>=0 
          && isOptSol([s1',s5',s10'],copie-1) 
          ensures isOptSol([s1+s1'+1,s5+s5',s10+s10'],nr)
  {
    assert isSol([s1',s5',s10'],copie-1);
    assert isSol([s1'+1,s5',s10'],copie);

    assert forall sol' :: |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0 
          && isSol(sol',copie-1) 
          ==> cost(sol') >= cost([s1',s5',s10']);
    assert isSol([s1+s1'+1,s5+s5',s10+s10'],nr);
    assert forall sol' :: |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0 
          && isSol(sol',nr) 
          ==> cost(sol') >= cost([s1+s1'+1,s5+s5',s10+s10']);
  }

  assert forall s1', s5', s10' :: s1'>=0 && s5'>=0 && s10'>=0 
          && isOptSol([s1',s5',s10'],copie-1) ==> 
          isOptSol([s1+s1'+1,s5+s5',s10+s10'],nr);
  

}

lemma exchangeArgument(nr: int,s1: int,s5: int,s10: int)
  requires nr >= 0  
  requires s1 >= 0
  requires s5 >= 0
  requires s10 >= 0
  requires isSol([s1,s5,s10],nr)
  ensures forall sol' :: |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0 && isSol(sol',nr) 
          ==> cost(sol') >= cost([s1,s5,s10]);
{
}

lemma caz2(copie: int,nr: int,s1: int,s5: int,s10: int)
  requires copie >= 5
  requires s1 >= 0
  requires s5 >= 0
  requires s10 >= 0
  requires INV(copie,nr,s1,s5,s10)
  ensures INV(copie-5,nr,s1,s5+1,s10)
{

 forall s1', s5', s10' | s1'>=0 && s5'>=0 && s10'>=0 
          && isOptSol([s1',s5',s10'],copie-5) 
          ensures isOptSol([s1+s1',s5+s5'+1,s10+s10'],nr)
  {
    assert isSol([s1',s5',s10'],copie-5);
    assert isSol([s1',s5'+1,s10'],copie);
    assert forall sol' :: |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0 && isSol(sol',copie-5) 
          ==> cost(sol') >= cost([s1',s5',s10']);
    assert isSol([s1+s1',s5+s5'+1,s10+s10'],nr);

    forall sol' | |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0
      ensures isSol(sol',nr)
    {
      exchangeArgument(nr,s1+s1',s5+s5'+1,s10+s10');
        if (cost(sol') < cost([s1+s1',s5+s5'+1,s10+s10']))
      {
        assume false;
      }

    }
    
    assert forall sol' :: |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0 && isSol(sol',nr)
          ==> cost(sol') >= cost([s1+s1',s5+s5'+1,s10+s10']);
  }



  assert forall s1', s5', s10' :: s1'>=0 && s5'>=0 && s10'>=0 
          && isOptSol([s1',s5',s10'],copie-5) ==> 
          isOptSol([s1+s1',s5+s5'+1,s10+s10'],nr);

}

lemma caz3(copie: int,nr: int,s1: int,s5: int,s10: int)
  requires copie >= 10
  requires s1 >= 0
  requires s5 >= 0
  requires s10 >= 0
  requires INV(copie,nr,s1,s5,s10)
  ensures INV(copie-10,nr,s1,s5,s10+1)
{
  assume false;
  // forall s1', s5', s10' | s1'>=0 && s5'>=0 && s10'>=0 
  //         && isOptSol([s1',s5',s10'],copie-10) 
  //         ensures isOptSol([s1+s1',s5+s5',s10+s10'+1],nr)
  // {
  //   assert isSol([s1',s5',s10'],copie-10);
  //   assert isSol([s1',s5',s10'+1],copie);

  //   assert forall sol' :: |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0 
  //         && isSol(sol',copie-10) 
  //         ==> cost(sol') >= cost([s1',s5',s10']);
  //   assert isSol([s1+s1',s5+s5',s10+s10'+1],nr);
  //   assert forall sol' :: |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0 && isSol(sol',nr) 
  //         ==> cost(sol') >= cost([s1+s1',s5+s5',s10+s10'+1]);
  // }

  // assert forall s1', s5', s10' :: s1'>=0 && s5'>=0 && s10'>=0 
  //         && isOptSol([s1',s5',s10'],copie-10) ==> 
  //         isOptSol([s1+s1',s5+s5',s10+s10'+1],nr);
}


  method bancnote(nr: int) returns (sol: seq<int>)
    requires nr>=0
    ensures |sol| == 3
    ensures sol[0]>=0
    ensures sol[1]>=0
    ensures sol[2]>=0
    ensures isSol(sol,nr)
    ensures isOptSol(sol,nr)
{
    var copie:=  nr;
    var s1 := 0;
    var s5 := 0;
    var s10 := 0;
    while(copie > 0)
      decreases copie
      invariant 0<=copie<=nr
      invariant isSol([s1,s5,s10],nr-copie)
      invariant INV(copie,nr,s1,s5,s10)
    {
        var i := 0;
        var s := findMax(copie);
        if( s == 1){
            caz1(copie,nr,s1,s5,s10);
            s1:=s1+1;
            assert isSol([s1,s5,s10],nr-(copie-1));
            assert INV(copie-1,nr,s1,s5,s10);
        }
        else{
            if(s == 5)
            {
                caz2(copie,nr,s1,s5,s10);
                s5:=s5+1;
                assert isSol([s1,s5,s10],nr-(copie-5));
                assert INV(copie-5,nr,s1,s5,s10);

            }
            else{
                caz3(copie,nr,s1,s5,s10);
                s10:=s10+1;
                assert isSol([s1,s5,s10],nr-(copie-10));
                assert INV(copie-10,nr,s1,s5,s10);

            }
        }
        copie := copie-s;
    }
    sol := [s1,s5,s10];
  }

  
method Main() {
  var nr:= 38;
  var sol:=bancnote(nr);
  print sol;
}