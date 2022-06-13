predicate esteSolutie(solutie : seq<int>, nr:int)
   requires |solutie| == 4
   requires solutie[0]>=0
   requires solutie[1]>=0
   requires solutie[2]>=0
   requires solutie[3]>=0
{
    solutie[0]*1+solutie[1]*5+solutie[2]*10+solutie[3]*20 == nr

}

function cost(solutie : seq<int>):int 
   requires |solutie| == 4
   requires solutie[0]>=0
   requires solutie[1]>=0
   requires solutie[2]>=0
   requires solutie[3]>=0
{
    solutie[0]+solutie[1]+solutie[2]+solutie[3]
}

predicate esteSolutieOptima(solutie : seq<int>, nr:int)
    requires |solutie| == 4
    requires solutie[0]>=0
    requires solutie[1]>=0
    requires solutie[2]>=0
    requires solutie[3]>=0
{   
  esteSolutie(solutie,nr) &&
  forall solutieOarecare :: |solutieOarecare| == 4 && solutieOarecare[0]>=0 && solutieOarecare[1]>=0 
        && solutieOarecare[2]>=0 && solutieOarecare[3]>=0 && esteSolutie(solutieOarecare,nr) 
          ==> cost(solutieOarecare) >= cost(solutie)

}

predicate INV(copie: int, nr: int, solutieFinala : seq<int>)
  requires |solutieFinala| == 4
  requires solutieFinala[0] >= 0
  requires solutieFinala[1] >= 0
  requires solutieFinala[2] >= 0
  requires solutieFinala[3] >= 0
{
   forall solutieCurenta :: |solutieCurenta| == 4 && solutieCurenta[0] >= 0 && solutieCurenta[1] >=0 && solutieCurenta[2]>=0 && solutieCurenta[3] >= 0 ==>
          (esteSolutie(solutieCurenta,copie) ==> 
          esteSolutie([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3]],nr)) &&
          (esteSolutieOptima(solutieCurenta,copie) ==> 
          esteSolutieOptima([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3]],nr))
}


method gasireMaxim(nr: int) returns(s:int)
  requires nr > 0
  ensures 0 < s <= nr
  ensures s == 1 || s == 5 || s == 10 || s == 20
  ensures s == 1 ==> nr < 5
  ensures s == 5 ==> 5 <= nr < 10
  ensures s == 10 ==> 10 <= nr < 20
  ensures s == 20 ==> nr >= 20
{
    if(nr >= 20)
    {
        s := 20;
    }
    else if(nr >= 10){
        s := 10;
        }
        else if(nr >= 5){
        s := 5;
            }
            else if(nr < 5){
                s := 1; 
            }

}


lemma cazMaxim1(copie: int, nr: int, solutieFinala: seq<int>)
  requires copie < 5
  requires |solutieFinala| == 4
  requires solutieFinala[0] >= 0
  requires solutieFinala[1] >= 0
  requires solutieFinala[2] >= 0
  requires solutieFinala[3] >= 0
  requires INV(copie,nr,solutieFinala)
  ensures INV(copie-1,nr,[(solutieFinala[0]+1),solutieFinala[1],solutieFinala[2],solutieFinala[3]])
{

  forall solutieCurenta | |solutieCurenta| == 4 && solutieCurenta[0] >= 0 && solutieCurenta[1] >=0 
          && solutieCurenta[2] >= 0  && solutieCurenta[3]>=0 && esteSolutieOptima(solutieCurenta,copie-1) 
          ensures esteSolutieOptima([solutieFinala[0]+solutieCurenta[0]+1,solutieFinala[1]+solutieCurenta[1],
          solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3]],nr)
  {
    assert esteSolutie(solutieCurenta,copie-1);
    assert esteSolutie([solutieCurenta[0]+1,solutieCurenta[1],solutieCurenta[2],solutieCurenta[3]],copie);

    assert forall solutieOarecare :: |solutieOarecare| == 4 && solutieOarecare[0]>=0 && solutieOarecare[1]>=0 
          && solutieOarecare[2]>=0 && solutieOarecare[3]>=0 && esteSolutie(solutieOarecare,copie-1) 
          ==> cost(solutieOarecare) >= cost(solutieCurenta);

    assert esteSolutie([solutieFinala[0]+solutieCurenta[0]+1,solutieFinala[1]+solutieCurenta[1],
          solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3]],nr);

    assert forall solutieOarecare :: |solutieOarecare| == 4 && solutieOarecare[0]>=0 && solutieOarecare[1]>=0 
          && solutieOarecare[2]>=0 && solutieOarecare[3]>=0 &&  esteSolutie(solutieOarecare,nr) 
          ==> cost(solutieOarecare) >= cost([solutieCurenta[0]+solutieFinala[0]+1,solutieCurenta[1]+solutieFinala[1],
          solutieCurenta[2]+solutieFinala[2],solutieCurenta[3]+solutieFinala[3]]);
  }

  assert forall solutieCurenta :: |solutieCurenta|==4 && solutieCurenta[0]>=0 && solutieCurenta[1]>=0 && solutieCurenta[2]>=0 && solutieCurenta[3]>=0 
          && esteSolutieOptima(solutieCurenta,copie-1) ==> 
          esteSolutieOptima([solutieFinala[0]+solutieCurenta[0]+1,solutieFinala[1]+solutieCurenta[1],
          solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3]],nr);

}

lemma cazMaxim5(copie: int, nr: int, solutieFinala: seq<int>)
  requires 5 <= copie < 10 
  requires |solutieFinala| == 4
  requires solutieFinala[0] >= 0
  requires solutieFinala[1] >= 0
  requires solutieFinala[2] >= 0
  requires solutieFinala[3] >= 0 
  requires INV(copie,nr,solutieFinala)
  ensures INV(copie-5,nr,[solutieFinala[0],(solutieFinala[1]+1),solutieFinala[2],solutieFinala[3]])
{

 forall solutieCurenta | |solutieCurenta| == 4 && solutieCurenta[0]>=0 && solutieCurenta[1]>=0 && 
          solutieCurenta[2]>=0 && solutieCurenta[3]>=0 && esteSolutieOptima(solutieCurenta,copie-5) 
          ensures esteSolutieOptima([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1]+1,
          solutieCurenta[2]+solutieFinala[2],solutieCurenta[3]+solutieFinala[3]],nr)
  {
    assert esteSolutie(solutieCurenta,copie-5);
    assert esteSolutie([solutieCurenta[0], solutieCurenta[1]+1,solutieCurenta[2],solutieCurenta[3]],copie);

    assert forall solutieOarecare :: |solutieOarecare| == 4 && solutieOarecare[0]>=0 && solutieOarecare[1]>=0 &&
          solutieOarecare[2]>=0 && solutieOarecare[3]>=0  && esteSolutie(solutieOarecare,copie-5) 
          ==> cost(solutieOarecare) >= cost(solutieCurenta);
    assert esteSolutie([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1]+1,solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3]],nr);
    
    assert forall solutieOarecare :: |solutieOarecare| == 4 && solutieOarecare[0]>=0 && solutieOarecare[1]>=0 && solutieOarecare[2]>=0 
          && solutieOarecare[3]>=0 && esteSolutie(solutieOarecare,nr)
          ==> cost(solutieOarecare) >= cost([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1]+1,solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3]]);
  }

  assert forall solutieCurenta :: |solutieCurenta| == 4 && solutieCurenta[0]>=0 && solutieCurenta[1]>=0 && solutieCurenta[2]>=0
          && solutieCurenta[3]>=0 && esteSolutie(solutieCurenta,copie-5) ==> 
          esteSolutieOptima([solutieCurenta[0]+solutieFinala[0],solutieCurenta[1]+solutieFinala[1]+1,solutieCurenta[2]+solutieFinala[2],solutieCurenta[3]+solutieFinala[3]],nr);

}

lemma cazMaxim10(copie: int, nr: int, solutieFinala: seq<int>)
  requires 10 <= copie < 20 
  requires |solutieFinala| == 4
  requires solutieFinala[0] >= 0
  requires solutieFinala[1] >= 0
  requires solutieFinala[2] >= 0
  requires solutieFinala[3] >= 0 
  requires INV(copie,nr,solutieFinala)
  ensures INV(copie-10,nr,[solutieFinala[0],solutieFinala[1],solutieFinala[2]+1,solutieFinala[3]])
{

 forall solutieCurenta | |solutieCurenta| == 4 && solutieCurenta[0]>=0 && solutieCurenta[1]>=0 && 
          solutieCurenta[2]>=0 && solutieCurenta[3]>=0 && esteSolutieOptima(solutieCurenta,copie-10) 
          ensures esteSolutieOptima([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],
          solutieCurenta[2]+solutieFinala[2]+1,solutieCurenta[3]+solutieFinala[3]],nr)
  {
    assert esteSolutie(solutieCurenta,copie-10);
    assert esteSolutie([solutieCurenta[0], solutieCurenta[1],solutieCurenta[2]+1,solutieCurenta[3]],copie);

    assert forall solutieOarecare :: |solutieOarecare| == 4 && solutieOarecare[0]>=0 && solutieOarecare[1]>=0 &&
          solutieOarecare[2]>=0 && solutieOarecare[3]>=0  && esteSolutie(solutieOarecare,copie-10) 
          ==> cost(solutieOarecare) >= cost(solutieCurenta);

    assert esteSolutie([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],1+solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3]],nr);

    assert forall solutieOarecare :: |solutieOarecare| == 4 && solutieOarecare[0]>=0 && solutieOarecare[1]>=0 
            && solutieOarecare[2]>=0 && solutieOarecare[3]>=0 && esteSolutie(solutieOarecare,nr)
          ==> cost(solutieOarecare) >= cost([solutieCurenta[0]+solutieFinala[0],solutieCurenta[1]+solutieFinala[1],
                                        solutieCurenta[2]+solutieFinala[2]+1,solutieCurenta[3]+solutieFinala[3]]);
  }

  assert forall solutieCurenta :: |solutieCurenta| == 4 && solutieCurenta[0]>=0 && solutieCurenta[1]>=0 && solutieCurenta[2]>=0
          && solutieCurenta[3]>=0 && esteSolutie(solutieCurenta,copie-10) ==> 
          esteSolutieOptima([solutieCurenta[0]+solutieFinala[0],solutieCurenta[1]+solutieFinala[1],
                            solutieCurenta[2]+solutieFinala[2]+1,solutieCurenta[3]+solutieFinala[3]],nr);

}



lemma B(copie:int,nr: int,solutieOarecare : seq<int>, solutieCurenta: seq<int>)
  requires |solutieOarecare| == 4
  requires solutieOarecare[0]>=0
  requires solutieOarecare[1]>=0
  requires solutieOarecare[2]>=0
  requires solutieOarecare[3]>=0
  requires |solutieCurenta| == 4
  requires solutieCurenta[0] >= 0
  requires solutieCurenta[1] >= 0
  requires solutieCurenta[2] >= 0
  requires solutieCurenta[3] >= 0
  requires copie >= 20
  requires esteSolutie(solutieOarecare,copie)
  requires esteSolutie(solutieCurenta,copie-20)
  requires esteSolutieOptima(solutieCurenta,copie-20)
  ensures cost(solutieOarecare) >= cost([solutieCurenta[0],solutieCurenta[1],solutieCurenta[2],1+solutieCurenta[3]])
  decreases solutieOarecare[0],solutieOarecare[1],solutieOarecare[2]
{
  assert esteSolutie(solutieOarecare,copie);
  assert esteSolutie([solutieCurenta[0],solutieCurenta[1],solutieCurenta[2],solutieCurenta[3]+1],copie);

  if(cost(solutieOarecare) < cost([solutieCurenta[0],solutieCurenta[1],solutieCurenta[2],1+solutieCurenta[3]]))
  {
    if(solutieOarecare[3] > (solutieCurenta[3]+1))
    {
      assert cost([solutieOarecare[0],solutieOarecare[1],solutieOarecare[2],solutieOarecare[3]-1]) < cost(solutieCurenta);
      assert esteSolutieOptima([solutieOarecare[0],solutieOarecare[1],solutieOarecare[2],solutieOarecare[3]-1],(copie-20));
      assert false;
      
    }
    else if(solutieOarecare[3] < solutieCurenta[3]+1)
      {
        assert (solutieOarecare[0]+(5*solutieOarecare[1])+(10*solutieOarecare[2]))>20;
        
        if(solutieOarecare[0]>=20)
        {
          var nouaSolutieOarecare := [solutieOarecare[0]-20,solutieOarecare[1],solutieOarecare[2],solutieOarecare[3]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[0]>=15 && solutieOarecare[1]>=1){
               var nouaSolutieOarecare := [solutieOarecare[0]-15,solutieOarecare[1]-1,solutieOarecare[2],solutieOarecare[3]+1];
                B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[0]>=10 && solutieOarecare[1]>=2){
               var nouaSolutieOarecare := [solutieOarecare[0]-10,solutieOarecare[1]-2,solutieOarecare[2],solutieOarecare[3]+1];
                B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[0]>=10 && solutieOarecare[2]>=1){
               var nouaSolutieOarecare := [solutieOarecare[0]-10,solutieOarecare[1],solutieOarecare[2]-1,solutieOarecare[3]+1];
                B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[0]>=5 && solutieOarecare[1]>=3){
               var nouaSolutieOarecare := [solutieOarecare[0]-5,solutieOarecare[1]-3,solutieOarecare[2],solutieOarecare[3]+1];
                B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[0]>=5 && solutieOarecare[1]>=1 && solutieOarecare[2]>=1){
               var nouaSolutieOarecare := [solutieOarecare[0]-5,solutieOarecare[1]-1,solutieOarecare[2]-1,solutieOarecare[3]+1];
                B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[1]>=2 && solutieOarecare[2]>=1){
               var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1]-2,solutieOarecare[2]-1,solutieOarecare[3]+1];
                B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        else{
               var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1],solutieOarecare[2]-2,solutieOarecare[3]+1];
                B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        
      }

    assert solutieOarecare[3] == (solutieCurenta[3]+1);

    if(solutieOarecare[2]>solutieCurenta[2])
    {
      assert cost([solutieOarecare[0],solutieOarecare[1],solutieOarecare[2],solutieOarecare[3]-1]) < cost(solutieCurenta);
      assert false;
    }
    else if(solutieOarecare[2] < solutieCurenta[2])
      {
        assert (solutieOarecare[0]+(5*solutieOarecare[1]))>10;

        if(solutieOarecare[0]>=10)
        {
          var nouaSolutieOarecare := [solutieOarecare[0]-10,solutieOarecare[1],solutieOarecare[2]+1,solutieOarecare[3]];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[1]>=2){
            var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1]-2,solutieOarecare[2]+1,solutieOarecare[3]];
             B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
          else
          {
            var nouaSolutieOarecare := [solutieOarecare[0]-5,solutieOarecare[1]-1,solutieOarecare[2]+1,solutieOarecare[3]];
             B(copie,nr,nouaSolutieOarecare, solutieCurenta);
          }
        }
        assert solutieOarecare[2] == solutieCurenta[2];

      if(solutieOarecare[1]>solutieCurenta[1])
    {
      assert cost([solutieOarecare[0],solutieOarecare[1],solutieOarecare[2],solutieOarecare[3]-1]) < cost(solutieCurenta);
      assert false;
    }
    else
    {
      if(solutieOarecare[1]<solutieCurenta[1])
      {
        assert solutieOarecare[0]>=5;
      
          var nouaSolutieOarecare := [solutieOarecare[0]-5,solutieOarecare[1]+1,solutieOarecare[2],solutieOarecare[3]];
          B(copie, nr, nouaSolutieOarecare, solutieCurenta);
        
      }
    }
    assert solutieOarecare[0]==solutieCurenta[0];
    assert false;

  }
}

lemma esteSolutiePentruCopie(copie:int,nr: int, solutieCurenta:seq<int>)
  requires |solutieCurenta| == 4
  requires solutieCurenta[0] >= 0
  requires solutieCurenta[1] >= 0
  requires solutieCurenta[2] >= 0
  requires solutieCurenta[3] >= 0
  requires copie >= 20
  requires esteSolutie(solutieCurenta,copie-20)
  requires esteSolutieOptima(solutieCurenta,copie-20)
  ensures esteSolutieOptima([solutieCurenta[0],solutieCurenta[1],solutieCurenta[2],1+solutieCurenta[3]],copie)
{
  forall solutieOarecare | |solutieOarecare| == 4 && solutieOarecare[0]>=0 && solutieOarecare[1]>=0 && 
        solutieOarecare[2]>=0 && solutieOarecare[3]>=0 && esteSolutie(solutieOarecare,copie)
    ensures cost(solutieOarecare)>=cost([solutieCurenta[0],solutieCurenta[1],solutieCurenta[2],1+solutieCurenta[3]])
  {
    B(copie,nr, solutieOarecare, solutieCurenta);
  }
  
}

lemma aux(copie: int ,nr: int, solutieOarecare : seq<int>, solutieFinala : seq<int>, solutieCurenta:seq<int>)
  requires |solutieOarecare| == 4
  requires solutieOarecare[0]>=0
  requires solutieOarecare[1]>=0
  requires solutieOarecare[2]>=0
  requires solutieOarecare[3]>=0
  requires |solutieFinala| == 4
  requires solutieFinala[0] >= 0
  requires solutieFinala[1] >= 0
  requires solutieFinala[2] >= 0
  requires solutieFinala[3] >= 0
  requires |solutieCurenta| == 4
  requires solutieCurenta[0] >= 0 
  requires solutieCurenta[1] >= 0
  requires solutieCurenta[2] >= 0
  requires solutieCurenta[3] >= 0
  requires copie >= 20
  requires esteSolutieOptima(solutieCurenta,copie-20)
  requires esteSolutie([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],1+solutieFinala[3]+solutieCurenta[3]],nr)
  requires esteSolutie(solutieOarecare,nr)
  requires INV(copie,nr,solutieFinala)
  ensures cost(solutieOarecare) >= cost([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],1+solutieFinala[3]+solutieCurenta[3]])
{
  esteSolutiePentruCopie(copie,nr,solutieCurenta);
}




lemma cazMaxim20(copie: int,nr: int, solutieFinala : seq<int>)
  requires copie >= 20
  requires |solutieFinala| == 4
  requires solutieFinala[0] >= 0
  requires solutieFinala[1] >= 0
  requires solutieFinala[2] >= 0
  requires solutieFinala[3] >= 0
  requires INV(copie,nr,solutieFinala)
  ensures INV(copie-20,nr,[solutieFinala[0],solutieFinala[1],solutieFinala[2],solutieFinala[3]+1])
{
  assert forall solutieCurenta :: |solutieCurenta|==4  && solutieCurenta[0]>=0 && solutieCurenta[1]>=0 && solutieCurenta[2]>=0 && solutieCurenta[3]>=0 ==>
          (esteSolutie(solutieCurenta,copie) ==> 
          esteSolutie([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3]],nr));

   forall solutieCurenta | |solutieCurenta| == 4  && solutieCurenta[0]>=0 && solutieCurenta[1]>=0 && solutieCurenta[2]>=0 && solutieCurenta[3]>=0 
          && esteSolutie(solutieCurenta,copie-20) 
          ensures esteSolutie([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3]+1],nr)
   {
     assert esteSolutie([solutieCurenta[0],solutieCurenta[1],solutieCurenta[2],solutieCurenta[3]+1],copie);
   }
  

  forall solutieCurenta | |solutieCurenta|==4 && solutieCurenta[0]>=0 && solutieCurenta[1]>=0 && solutieCurenta[2]>=0 && solutieCurenta[3]>=0 
          && esteSolutieOptima(solutieCurenta,copie-20) 
          ensures esteSolutieOptima([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3]+1],nr)
  {

    assert esteSolutie(solutieCurenta,copie-20);
    assert esteSolutie([solutieCurenta[0],solutieCurenta[1],solutieCurenta[2],solutieCurenta[3]+1],copie);

    assert forall solutieOarecare :: |solutieOarecare| == 4 && solutieOarecare[0]>=0 && solutieOarecare[1]>=0 && solutieOarecare[2]>=0 && solutieOarecare[3]>=0
          && esteSolutie(solutieOarecare,copie-20) 
          ==> cost(solutieOarecare) >= cost(solutieCurenta);


    assert esteSolutie([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3]+1],nr);

    forall solutieOarecare | |solutieOarecare| == 4 && solutieOarecare[0]>=0 && solutieOarecare[1]>=0 && solutieOarecare[2]>=0 && solutieOarecare[3]>=0
                 && esteSolutie(solutieOarecare,nr)
      ensures cost(solutieOarecare) >= cost([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],1+solutieFinala[3]+solutieCurenta[3]])
      {
          aux(copie, nr, solutieOarecare, solutieFinala, solutieCurenta);
      }

    assert forall solutieOarecare :: |solutieOarecare| == 4 && solutieOarecare[0]>=0 && solutieOarecare[1]>=0 && solutieOarecare[2]>=0 && solutieOarecare[3]>=0
             && esteSolutie(solutieOarecare,nr) 
          ==> cost(solutieOarecare) >= cost([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],1+solutieFinala[3]+solutieCurenta[3]]);
  }


  assert forall solutieCurenta :: |solutieCurenta| == 4 && solutieCurenta[0]>=0 && solutieCurenta[1]>=0 && solutieCurenta[2]>=0 && solutieCurenta[3]>=0
          && esteSolutieOptima(solutieCurenta,copie-20) ==> 
          esteSolutieOptima([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],1+solutieFinala[3]+solutieCurenta[3]],nr);


  assert forall solutieCurenta :: |solutieCurenta| == 4 && solutieCurenta[0]>=0 && solutieCurenta[1]>=0 && solutieCurenta[2]>=0 && solutieCurenta[3]>=0 ==>
          (esteSolutie(solutieCurenta,copie-20) ==> 
          esteSolutie([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],1+solutieFinala[3]+solutieCurenta[3]],nr));
  
  assert forall solutieCurenta :: |solutieCurenta| == 4 && solutieCurenta[0]>=0 && solutieCurenta[1]>=0 && solutieCurenta[2]>=0 && solutieCurenta[3] >= 0 ==>        
          (esteSolutieOptima(solutieCurenta,copie-20) ==> 
          esteSolutieOptima([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3]+1],nr));

  assert  INV(copie-20,nr,[solutieFinala[0],solutieFinala[1],solutieFinala[2],1+solutieFinala[3]]);
}



  method nrMinimBancnote(nr: int) returns (solutie: seq<int>)
    requires nr>=0
    ensures |solutie| == 4
    ensures solutie[0]>=0
    ensures solutie[1]>=0
    ensures solutie[2]>=0
    ensures solutie[3]>=0
    ensures esteSolutie(solutie,nr)
    ensures esteSolutieOptima(solutie,nr)
{

    var copie:=  nr;
    var s1 := 0;
    var s5 := 0;
    var s10 := 0;
    var s20 := 0;
    while(copie > 0)
      decreases copie
      invariant 0<=copie<=nr
      invariant esteSolutie([s1,s5,s10,s20],nr-copie)
      invariant INV(copie,nr,[s1,s5,s10,s20])
    {
        var i := 0;
        var s := gasireMaxim(copie);
        if( s == 1){
            cazMaxim1(copie,nr,[s1,s5,s10,s20]);
            s1:=s1+1;
            assert esteSolutie([s1,s5,s10,s20],nr-(copie-1));
            assert INV(copie-1,nr,[s1,s5,s10,s20]);
        }
        else if(s == 5)
            {
                cazMaxim5(copie,nr,[s1,s5,s10,s20]);
                s5:=s5+1;
                assert esteSolutie([s1,s5,s10,s20],nr-(copie-5));
                assert INV(copie-5,nr,[s1,s5,s10,s20]);

            }
            else if (s == 10){
                cazMaxim10(copie,nr,[s1,s5,s10,s20]);
                s10:=s10+1;
                assert esteSolutie([s1,s5,s10,s20],nr-(copie-10));
                assert INV(copie-10,nr,[s1,s5,s10,s20]);

            }
            else{
                cazMaxim20(copie,nr,[s1,s5,s10,s20]);
                s20:=s20+1;
                assert esteSolutie([s1,s5,s10,s20],nr-(copie-20));
                assert INV(copie-20,nr,[s1,s5,s10,s20]);
            }

        copie := copie-s;
    }
    solutie := [s1,s5,s10,s20];
}


method Main() {
  var nr:= 18;
  var sol:=nrMinimBancnote(nr);
  print sol;
}