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
  ensures s == 5 ==> 5 <= nr < 10
  ensures s == 10 ==> nr >= 10
  
{
  if(nr >= 10){
    s := 10;
  }
  else
  {
    if(nr >= 5){
    s := 5;
  }
    else{
       if(nr < 5){
        s := 1; 
        }
    }
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

// lemma exchangeArgument(nr: int,s1: int,s5: int,s10: int)
//   requires nr >= 0  
//   requires s1 >= 0
//   requires s5 >= 0
//   requires s10 >= 0
//   requires isSol([s1,s5,s10],nr)
//   ensures forall sol' :: |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0 ==> isSol(sol',nr)
//   ensures forall sol' :: |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0 && isSol(sol',nr)
//           ==> cost(sol') >= cost([s1,s5,s10])
// {
// }

lemma caz2(copie: int,nr: int,s1: int,s5: int,s10: int)
  requires 5 <= copie < 10 
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

    // forall sol' | |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0
    //   ensures isSol(sol',nr)
    // {
    //     exchangeArgument(nr,s1+s1',s5+s5'+1,s10+s10');
    //     if (cost(sol') < cost([s1+s1',s5+s5'+1,s10+s10']))
    //   {
    //     assume false;
    //   }

    // }
    
    assert forall sol' :: |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0 && isSol(sol',nr)
          ==> cost(sol') >= cost([s1+s1',s5+s5'+1,s10+s10']);
  }

  assert forall s1', s5', s10' :: s1'>=0 && s5'>=0 && s10'>=0 
          && isOptSol([s1',s5',s10'],copie-5) ==> 
          isOptSol([s1+s1',s5+s5'+1,s10+s10'],nr);

}


lemma B(copie:int,nr: int,sol' : seq<int>, s1': int, s5' :int, s10':int)
  requires |sol'| == 3
  requires sol'[0]>=0
  requires sol'[1]>=0
  requires sol'[2]>=0
  requires s1' >= 0
  requires s5' >= 0
  requires s10' >= 0
  requires copie >=10
  requires isSol(sol',copie)
  requires isSol([s1',s5',s10'],copie-10)
  requires isOptSol([s1',s5',s10'],copie-10)
  ensures cost(sol') >= cost([s1',s5',(s10'+1)])
  decreases sol'[0],sol'[1]
{
  assert isSol(sol',copie);
  assert isSol([s1',s5',(s10'+1)],copie);

  if(cost(sol') < cost([s1',s5',(s10'+1)]))
  {
    if(sol'[2] > (s10'+1))
    {
      assert cost([sol'[0],sol'[1],(sol'[2]-1)]) < cost([s1',s5',s10']);
      assert isOptSol([sol'[0],sol'[1],(sol'[2]-1)],(copie-10));
      assert false;
    }
    else
    {
      if(sol'[2]<s10'+1)
      {
        assert (sol'[0]+(5*sol'[1]))>10;

        if(sol'[0]>=10)
        {
          var sol'' := [sol'[0]-10,sol'[1],sol'[2]+1];
          B(copie,nr,sol'', s1', s5', s10');
        }
        else{
          if(sol'[1]>=2){
            var sol'' := [sol'[0],sol'[1]-2,sol'[2]+1];
             B(copie,nr,sol'', s1', s5', s10');
          }
          else
          {
            var sol'' := [sol'[0]-5,sol'[1]-1,sol'[2]+1];
             B(copie,nr,sol'', s1', s5', s10');
          }
        }
      }
    }
    assert sol'[2] == (s10'+1);

    if(sol'[1]>s5')
    {
      assert cost([sol'[0],sol'[1],(sol'[2]-1)]) < cost([s1',s5',s10']);
      assert false;
    }
    else
    {
      if(sol'[1]<s5')
      {
        assert sol'[0]>=5;
      
          var sol'' := [sol'[0]-5,sol'[1]+1,sol'[2]];
          B(copie, nr, sol'', s1', s5', s10');
        
      }
    }

    assert sol'[1] == s5';

    assert sol'[0]==s1';
    
    assert false;
  }
}

lemma solCopie(copie:int,nr: int,sol':seq<int>, s1': int, s5' :int, s10':int)
  requires |sol'| == 3
  requires sol'[0]>=0
  requires sol'[1]>=0
  requires sol'[2]>=0
  requires s1' >= 0
  requires s5' >= 0
  requires s10' >= 0
  requires copie >=10
  requires isSol([s1',s5',s10'],copie-10)
  requires isOptSol([s1',s5',s10'],copie-10)
  ensures isOptSol([s1',s5',s10'+1],copie)
{
  forall sol' | |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0 && isSol(sol',copie)
    ensures cost(sol')>=cost([s1',s5',(s10'+1)])
  {
    B(copie,nr, sol' ,s1', s5',s10');
  }
  
}

lemma aux(copie: int ,nr: int, sol' : seq<int>, s1 : int, s1' : int, s5 : int, s5' : int, s10 : int, s10':int)
  requires |sol'| == 3
  requires sol'[0]>=0
  requires sol'[1]>=0
  requires sol'[2]>=0
  requires s1 >= 0
  requires s5 >= 0
  requires s10 >= 0
  requires s1' >= 0 
  requires s5' >= 0
  requires s10' >= 0
  requires copie >= 10 
  requires isOptSol([s1',s5',s10'],copie-10)
  requires isSol([s1+s1',s5+s5',s10+s10'+1],nr)
  requires isSol(sol',nr)
  requires INV(copie,nr,s1,s5,s10)
  ensures cost(sol') >= cost([s1+s1',s5+s5',s10+s10'+1])
{
  solCopie(copie,nr,sol',s1', s5', s10');
}

lemma caz3(copie: int,nr: int,s1: int,s5: int,s10: int)
  requires copie >= 10
  requires s1 >= 0
  requires s5 >= 0
  requires s10 >= 0
  requires INV(copie,nr,s1,s5,s10)
  ensures INV(copie-10,nr,s1,s5,s10+1)
{
  assert forall s1', s5', s10' :: s1'>=0 && s5'>=0 && s10'>=0 ==>
          (isSol([s1',s5',s10'],copie) ==> 
          isSol([s1+s1',s5+s5',s10+s10'],nr));

   forall s1', s5', s10' | s1'>=0 && s5'>=0 && s10'>=0 
          && isSol([s1',s5',s10'],copie-10) 
          ensures isSol([s1+s1',s5+s5',s10+s10'+1],nr)
   {
     assert isSol([s1',s5',s10'+1],copie);
   }
  

  forall s1', s5', s10' | s1'>=0 && s5'>=0 && s10'>=0 
          && isOptSol([s1',s5',s10'],copie-10) 
          ensures isOptSol([s1+s1',s5+s5',s10+s10'+1],nr)
  {

    assert isSol([s1',s5',s10'],copie-10);
    assert isSol([s1',s5',s10'+1],copie);

    assert forall sol' :: |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0 
          && isSol(sol',copie-10) 
          ==> cost(sol') >= cost([s1',s5',s10']);


    assert isSol([s1+s1',s5+s5',s10+s10'+1],nr);

    forall sol' | |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0 && isSol(sol',nr)
      ensures cost(sol') >= cost([s1+s1',s5+s5',s10+s10'+1])
      {
          aux(copie, nr, sol', s1, s1', s5, s5', s10, s10');
      }
   
    assert forall sol' :: |sol'| == 3 && sol'[0]>=0 && sol'[1]>=0 && sol'[2]>=0 && isSol(sol',nr) 
          ==> cost(sol') >= cost([s1+s1',s5+s5',s10+s10'+1]);
  }


  assert forall s1', s5', s10' :: s1'>=0 && s5'>=0 && s10'>=0 
          && isOptSol([s1',s5',s10'],copie-10) ==> 
          isOptSol([s1+s1',s5+s5',s10+s10'+1],nr);

  assert forall s1', s5', s10' :: s1'>=0 && s5'>=0 && s10'>=0 ==>
          (isSol([s1',s5',s10'],copie-10) ==> 
          isSol([s1+s1',s5+s5',s10+s10'+1],nr));
  
  assert forall s1', s5', s10' :: s1'>=0 && s5'>=0 && s10'>=0 ==>        
          (isOptSol([s1',s5',s10'],copie-10) ==> 
          isOptSol([s1+s1',s5+s5',s10+s10'+1],nr));

  assert  INV(copie-10,nr,s1,s5,s10+1);
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