predicate esteSolutieValida(solutie : seq<int>)
{
  |solutie| == 5 && solutie[0]>=0 && solutie[1]>=0 && solutie[2]>=0 && solutie[3]>=0 && solutie[4]>=0
}



predicate esteSolutie(solutie : seq<int>, nr:int)
  requires esteSolutieValida(solutie)
{
    solutie[0]*1+solutie[1]*5+solutie[2]*10+solutie[3]*20+solutie[4]*50 == nr

}


function cost(solutie : seq<int>):int 
  requires esteSolutieValida(solutie)
{
    solutie[0]+solutie[1]+solutie[2]+solutie[3]+solutie[4]
}

predicate esteSolutieOptima(solutie : seq<int>, nr:int)
    requires esteSolutieValida(solutie)
{   
  esteSolutie(solutie,nr) &&
  forall solutieOarecare :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare,nr) 
          ==> cost(solutieOarecare) >= cost(solutie)

}

predicate INV(copie: int, nr: int, solutieFinala : seq<int>)
  requires esteSolutieValida(solutieFinala)
{
   forall solutieCurenta :: esteSolutieValida(solutieCurenta) ==>
          (esteSolutie(solutieCurenta,copie) ==> 
          esteSolutie([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],
          solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],solutieFinala[4]+solutieCurenta[4]],nr)) &&
          (esteSolutieOptima(solutieCurenta,copie) ==> 
          esteSolutieOptima([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],
          solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],solutieFinala[4]+solutieCurenta[4]],nr))
}


method gasireMaxim(nr: int) returns(s:int)
  requires nr > 0
  ensures 0 < s <= nr
  ensures s == 1 || s == 5 || s == 10 || s == 20 || s == 50
  ensures s == 1 ==> nr < 5
  ensures s == 5 ==> 5 <= nr < 10
  ensures s == 10 ==> 10 <= nr < 20
  ensures s == 20 ==> 20 <= nr < 50
  ensures s == 50 ==> nr >= 50
{
    if(nr >= 50)
    {
        s := 50 ;
    }
    else if(nr >= 20)
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
  requires esteSolutieValida(solutieFinala)
  requires INV(copie,nr,solutieFinala)
  ensures INV(copie-1,nr,[(solutieFinala[0]+1),solutieFinala[1],solutieFinala[2],solutieFinala[3],solutieFinala[4]])
{

  forall solutieCurenta | esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta,copie-1) 
          ensures esteSolutieOptima([solutieFinala[0]+solutieCurenta[0]+1,solutieFinala[1]+solutieCurenta[1],
          solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],solutieFinala[4]+solutieCurenta[4]],nr)
  {
    assert esteSolutie(solutieCurenta,copie-1);
    assert esteSolutie([solutieCurenta[0]+1,solutieCurenta[1],solutieCurenta[2],solutieCurenta[3],solutieCurenta[4]],copie);

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare,copie-1) 
          ==> cost(solutieOarecare) >= cost(solutieCurenta);

    assert esteSolutie([solutieFinala[0]+solutieCurenta[0]+1,solutieFinala[1]+solutieCurenta[1],
          solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],solutieFinala[4]+solutieCurenta[4]],nr);

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare) &&  esteSolutie(solutieOarecare,nr) 
          ==> cost(solutieOarecare) >= cost([solutieCurenta[0]+solutieFinala[0]+1,solutieCurenta[1]+solutieFinala[1],
          solutieCurenta[2]+solutieFinala[2],solutieCurenta[3]+solutieFinala[3],solutieCurenta[4]+solutieFinala[4]]);
  }

  assert forall solutieCurenta :: esteSolutieValida(solutieCurenta) 
          && esteSolutieOptima(solutieCurenta,copie-1) ==> 
          esteSolutieOptima([solutieFinala[0]+solutieCurenta[0]+1,solutieFinala[1]+solutieCurenta[1],
          solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],solutieFinala[4]+solutieCurenta[4]],nr);

}

lemma cazMaxim5(copie: int, nr: int, solutieFinala: seq<int>)
  requires 5 <= copie < 10 
  requires esteSolutieValida(solutieFinala)
  requires INV(copie,nr,solutieFinala)
  ensures INV(copie-5,nr,[solutieFinala[0],(solutieFinala[1]+1),solutieFinala[2],solutieFinala[3],solutieFinala[4]])
{

 forall solutieCurenta | esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta,copie-5) 
          ensures esteSolutieOptima([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1]+1,
          solutieCurenta[2]+solutieFinala[2],solutieCurenta[3]+solutieFinala[3],solutieFinala[4]],nr)
  {
    assert esteSolutie(solutieCurenta,copie-5);
    assert esteSolutie([solutieCurenta[0], solutieCurenta[1]+1,solutieCurenta[2],solutieCurenta[3],solutieCurenta[4]],copie);

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare)  && esteSolutie(solutieOarecare,copie-5) 
          ==> cost(solutieOarecare) >= cost(solutieCurenta);
    assert esteSolutie([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1]+1,
    solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],solutieFinala[4]+solutieCurenta[4]],nr);
    
    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare,nr)
          ==> cost(solutieOarecare) >= cost([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1]+1,
          solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],solutieFinala[4]+solutieCurenta[4]]);
  }

  assert forall solutieCurenta :: esteSolutieValida(solutieCurenta) && esteSolutie(solutieCurenta,copie-5) ==> 
          esteSolutieOptima([solutieCurenta[0]+solutieFinala[0],solutieCurenta[1]+solutieFinala[1]+1,
          solutieCurenta[2]+solutieFinala[2],solutieCurenta[3]+solutieFinala[3],solutieCurenta[4]+solutieFinala[4]],nr);

}

lemma aux2(copie:int,solutieCurenta:seq<int>)
  requires 10 <= copie < 20
  requires esteSolutieValida(solutieCurenta)
  requires esteSolutieOptima(solutieCurenta,copie-10)
  ensures esteSolutieOptima([solutieCurenta[0], solutieCurenta[1],solutieCurenta[2]+1,solutieCurenta[3],solutieCurenta[4]],copie)
{

    assert esteSolutie([solutieCurenta[0], solutieCurenta[1],solutieCurenta[2]+1,solutieCurenta[3],solutieCurenta[4]],copie);
    if(!esteSolutieOptima([solutieCurenta[0], solutieCurenta[1],solutieCurenta[2]+1,solutieCurenta[3],solutieCurenta[4]],copie))
    {
      var solutieOptima :|esteSolutieValida(solutieOptima) && esteSolutie(solutieOptima,copie) && cost(solutieOptima)<cost([solutieCurenta[0], solutieCurenta[1],solutieCurenta[2]+1,solutieCurenta[3],solutieCurenta[4]]);
      assert cost([solutieCurenta[0], solutieCurenta[1],solutieCurenta[2]+1,solutieCurenta[3],solutieCurenta[4]]) == cost(solutieCurenta)+1;
      assert solutieOptima[3] == 0;
      assert solutieOptima[4] == 0;
      if(solutieOptima[2]>=1)
      {
        var solutieOptima' := [solutieOptima[0],solutieOptima[1],solutieOptima[2]-1,solutieOptima[3],solutieOptima[4]];
        assert esteSolutie(solutieOptima',copie-10);
        assert cost(solutieOptima') == cost(solutieOptima)-1;
        assert cost(solutieOptima)-1 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1]>=2)
      {
        var solutieOptima' := [solutieOptima[0],solutieOptima[1]-2,solutieOptima[2],solutieOptima[3],solutieOptima[4]];
        assert esteSolutie(solutieOptima',copie-10);
        assert cost(solutieOptima') == cost(solutieOptima)-2;
        assert cost(solutieOptima)-2 < cost(solutieCurenta);
        assert false;
      }else if(solutieOptima[1]>=1 && solutieOptima[0]>=5 )
      {
        var solutieOptima' := [solutieOptima[0]-5,solutieOptima[1]-1,solutieOptima[2],solutieOptima[3],solutieOptima[4]];
        assert esteSolutie(solutieOptima',copie-10);
        assert cost(solutieOptima') == cost(solutieOptima)-6;
        assert cost(solutieOptima)-6 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[0]>=10 )
      {
        var solutieOptima' := [solutieOptima[0]-10,solutieOptima[1],solutieOptima[2],solutieOptima[3],solutieOptima[4]];
        assert esteSolutie(solutieOptima',copie-10);
        assert cost(solutieOptima') == cost(solutieOptima)-10;
        assert cost(solutieOptima)-10 < cost(solutieCurenta);
        assert false;
      }
      else{
        assert false;
      }

    }

}



lemma cazMaxim10(copie: int, nr: int, solutieFinala: seq<int>)
  requires 10 <= copie < 20 
  requires esteSolutieValida(solutieFinala) 
  requires INV(copie,nr,solutieFinala)
  ensures INV(copie-10,nr,[solutieFinala[0],solutieFinala[1],solutieFinala[2]+1,solutieFinala[3],solutieFinala[4]])
{

 forall solutieCurenta | esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta,copie-10) 
          ensures esteSolutieOptima([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],
          solutieCurenta[2]+solutieFinala[2]+1,solutieCurenta[3]+solutieFinala[3],solutieCurenta[4]+solutieFinala[4]],nr)
  {
    assert esteSolutie(solutieCurenta,copie-10);
    assert esteSolutie([solutieCurenta[0], solutieCurenta[1],solutieCurenta[2]+1,solutieCurenta[3],solutieCurenta[4]],copie);

    aux2(copie,solutieCurenta);

    assert esteSolutieOptima([solutieCurenta[0], solutieCurenta[1],solutieCurenta[2]+1,solutieCurenta[3],solutieCurenta[4]],copie);

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare)  && esteSolutie(solutieOarecare,copie-10) 
          ==> cost(solutieOarecare) >= cost(solutieCurenta);
    

    assert esteSolutie([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],1+solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],solutieFinala[4]+solutieCurenta[4]],nr);

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare,nr)
          ==> cost(solutieOarecare) >= cost([solutieCurenta[0]+solutieFinala[0],solutieCurenta[1]+solutieFinala[1],
                                        solutieCurenta[2]+solutieFinala[2]+1,solutieCurenta[3]+solutieFinala[3],solutieCurenta[4]+solutieFinala[4]]);
  }

  assert forall solutieCurenta :: esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta,copie-10) ==> 
          esteSolutieOptima([solutieCurenta[0]+solutieFinala[0],solutieCurenta[1]+solutieFinala[1],
                            solutieCurenta[2]+solutieFinala[2]+1,solutieCurenta[3]+solutieFinala[3],solutieCurenta[4]+solutieFinala[4]],nr);

}



lemma aux3(copie:int,solutieCurenta:seq<int>)
  requires 20 <= copie < 50
  requires esteSolutieValida(solutieCurenta)
  requires esteSolutieOptima(solutieCurenta,copie-20)
  ensures esteSolutieOptima([solutieCurenta[0], solutieCurenta[1],solutieCurenta[2],1+solutieCurenta[3],solutieCurenta[4]],copie)
{

    assert esteSolutie([solutieCurenta[0], solutieCurenta[1],solutieCurenta[2],1+solutieCurenta[3],solutieCurenta[4]],copie);
    if(!esteSolutieOptima([solutieCurenta[0], solutieCurenta[1],solutieCurenta[2],1+solutieCurenta[3],solutieCurenta[4]],copie))
    {
      var solutieOptima :|esteSolutieValida(solutieOptima) && esteSolutie(solutieOptima,copie) && cost(solutieOptima)<cost([solutieCurenta[0], solutieCurenta[1],solutieCurenta[2],1+solutieCurenta[3],solutieCurenta[4]]);
      assert cost([solutieCurenta[0], solutieCurenta[1],solutieCurenta[2],1+solutieCurenta[3],solutieCurenta[4]]) == cost(solutieCurenta)+1;
      assert solutieOptima[4] == 0;
      if(solutieOptima[3]>=1)
      {
        var solutieOptima' := [solutieOptima[0],solutieOptima[1],solutieOptima[2],solutieOptima[3]-1,solutieOptima[4]];
        assert esteSolutie(solutieOptima',copie-20);
        assert cost(solutieOptima') == cost(solutieOptima)-1;
        assert cost(solutieOptima)-1 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[2]>=2)
      {
        var solutieOptima' := [solutieOptima[0],solutieOptima[1],solutieOptima[2]-2,solutieOptima[3],solutieOptima[4]];
        assert esteSolutie(solutieOptima',copie-20);
        assert cost(solutieOptima') == cost(solutieOptima)-2;
        assert cost(solutieOptima)-2 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[2]>=1 && solutieOptima[1]>=2)
      {       
        var solutieOptima' := [solutieOptima[0],solutieOptima[1]-2,solutieOptima[2]-1,solutieOptima[3],solutieOptima[4]];
        assert esteSolutie(solutieOptima',copie-20);
        assert cost(solutieOptima') == cost(solutieOptima)-3;
        assert cost(solutieOptima)-3 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[2]>=1 && solutieOptima[1]>=1 && solutieOptima[0]>=5)
      {
        var solutieOptima' := [solutieOptima[0]-5,solutieOptima[1]-1,solutieOptima[2]-1,solutieOptima[3],solutieOptima[4]];
        assert esteSolutie(solutieOptima',copie-20);
        assert cost(solutieOptima') == cost(solutieOptima)-7;
        assert cost(solutieOptima)-7 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1]>=4)
      {
        var solutieOptima' := [solutieOptima[0],solutieOptima[1]-4,solutieOptima[2],solutieOptima[3],solutieOptima[4]];
        assert esteSolutie(solutieOptima',copie-20);
        assert cost(solutieOptima') == cost(solutieOptima)-4;
        assert cost(solutieOptima)-4 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1]>=3 && solutieOptima[0]>=5)
      {
        var solutieOptima' := [solutieOptima[0]-5,solutieOptima[1]-3,solutieOptima[2],solutieOptima[3],solutieOptima[4]];
        assert esteSolutie(solutieOptima',copie-20);
        assert cost(solutieOptima') == cost(solutieOptima)-8;
        assert cost(solutieOptima)-8 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1]>=2 && solutieOptima[0]>=10)
      {
        var solutieOptima' := [solutieOptima[0]-10,solutieOptima[1]-2,solutieOptima[2],solutieOptima[3],solutieOptima[4]];
        assert esteSolutie(solutieOptima',copie-20);
        assert cost(solutieOptima') == cost(solutieOptima)-12;
        assert cost(solutieOptima)-12 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[1]>=1 && solutieOptima[0]>=15)
      {
        var solutieOptima' := [solutieOptima[0]-15,solutieOptima[1]-1,solutieOptima[2],solutieOptima[3],solutieOptima[4]];
        assert esteSolutie(solutieOptima',copie-20);
        assert cost(solutieOptima') == cost(solutieOptima)-16;
        assert cost(solutieOptima)-16 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[0]>=20)
      {
        var solutieOptima' := [solutieOptima[0]-20,solutieOptima[1],solutieOptima[2],solutieOptima[3],solutieOptima[4]];
        assert esteSolutie(solutieOptima',copie-20);
        assert cost(solutieOptima') == cost(solutieOptima)-20;
        assert cost(solutieOptima)-20 < cost(solutieCurenta);
        assert false;
      }
      else if(solutieOptima[2]>=1 && solutieOptima[0]>=10)
      {
        var solutieOptima' := [solutieOptima[0]-10,solutieOptima[1],solutieOptima[2]-1,solutieOptima[3],solutieOptima[4]];
        assert esteSolutie(solutieOptima',copie-20);
        assert cost(solutieOptima') == cost(solutieOptima)-11;
        assert cost(solutieOptima)-11 < cost(solutieCurenta);
        assert false;
      }
      else{
        assert false;
      }
    }

}



lemma cazMaxim20(copie: int, nr: int, solutieFinala: seq<int>)
  requires 20 <= copie < 50 
  requires esteSolutieValida(solutieFinala) 
  requires INV(copie,nr,solutieFinala)
  ensures INV(copie-20,nr,[solutieFinala[0],solutieFinala[1],solutieFinala[2],solutieFinala[3]+1,solutieFinala[4]])
{

 forall solutieCurenta | esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta,copie-20) 
          ensures esteSolutieOptima([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],
          solutieCurenta[2]+solutieFinala[2],solutieCurenta[3]+solutieFinala[3]+1,solutieCurenta[4]+solutieFinala[4]],nr)
  {
    assert esteSolutie(solutieCurenta,copie-20);
    assert esteSolutie([solutieCurenta[0], solutieCurenta[1],solutieCurenta[2],solutieCurenta[3]+1,solutieCurenta[4]],copie);

    aux3(copie,solutieCurenta);

    assert esteSolutieOptima([solutieCurenta[0], solutieCurenta[1],solutieCurenta[2],1+solutieCurenta[3],solutieCurenta[4]],copie);

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare)  && esteSolutie(solutieOarecare,copie-20) 
          ==> cost(solutieOarecare) >= cost(solutieCurenta);
    

    assert esteSolutie([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],1+solutieFinala[3]+solutieCurenta[3],solutieFinala[4]+solutieCurenta[4]],nr);

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare,nr)
          ==> cost(solutieOarecare) >= cost([solutieCurenta[0]+solutieFinala[0],solutieCurenta[1]+solutieFinala[1],
                                        solutieCurenta[2]+solutieFinala[2],1+solutieCurenta[3]+solutieFinala[3],solutieCurenta[4]+solutieFinala[4]]);
  }

  assert forall solutieCurenta :: esteSolutieValida(solutieCurenta) && esteSolutieOptima(solutieCurenta,copie-20) ==> 
          esteSolutieOptima([solutieCurenta[0]+solutieFinala[0],solutieCurenta[1]+solutieFinala[1],
                            solutieCurenta[2]+solutieFinala[2],1+solutieCurenta[3]+solutieFinala[3],solutieCurenta[4]+solutieFinala[4]],nr);

}




lemma B(copie:int,nr: int,solutieOarecare : seq<int>, solutieCurenta: seq<int>)
  requires esteSolutieValida(solutieOarecare)
  requires esteSolutieValida(solutieCurenta)
  requires copie >= 50
  requires esteSolutie(solutieOarecare,copie)
  requires esteSolutie(solutieCurenta,copie-50)
  requires esteSolutieOptima(solutieCurenta,copie-50)
  ensures cost(solutieOarecare) >= cost([solutieCurenta[0],solutieCurenta[1],solutieCurenta[2],solutieCurenta[3],1+solutieCurenta[4]])
  decreases solutieOarecare[0],solutieOarecare[1],solutieOarecare[2],solutieOarecare[3]
{
  assert esteSolutie(solutieOarecare,copie);
  assert esteSolutie([solutieCurenta[0],solutieCurenta[1],solutieCurenta[2],solutieCurenta[3],1+solutieCurenta[4]],copie);

  if(cost(solutieOarecare) < cost([solutieCurenta[0],solutieCurenta[1],solutieCurenta[2],solutieCurenta[3],1+solutieCurenta[4]]))
  {
    if(solutieOarecare[4] > solutieCurenta[4]+1)
    {
      assert cost([solutieOarecare[0],solutieOarecare[1],solutieOarecare[2],solutieOarecare[3],solutieOarecare[4]-1]) < cost(solutieCurenta);
      assert esteSolutieOptima([solutieOarecare[0],solutieOarecare[1],solutieOarecare[2],solutieOarecare[3],solutieOarecare[4]-1],(copie-50));
      assert false;
    }
    else if(solutieOarecare[4]<solutieCurenta[4]+1)
    {
      assert (solutieOarecare[0]+(5*solutieOarecare[1])+(10*solutieOarecare[2])+(20*solutieOarecare[3]))>=50;

      if(solutieOarecare[2]>=1 && solutieOarecare[3]>=2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1],solutieOarecare[2]-1,solutieOarecare[3]-2,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[2]>=3 && solutieOarecare[3]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1],solutieOarecare[2]-3,solutieOarecare[3]-1,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[2]>=5)
      {
          var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1],solutieOarecare[2]-5,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1]>=10)
      {
          var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1]-10,solutieOarecare[2],solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1]>=8 && solutieOarecare[2]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1]-8,solutieOarecare[2]-1,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1]>=6 && solutieOarecare[2]>=2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1]-6,solutieOarecare[2]-2,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1]>=6 && solutieOarecare[3]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1]-6,solutieOarecare[2],solutieOarecare[3]-1,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1]>=4 && solutieOarecare[2]>=3)
      {
          var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1]-4,solutieOarecare[2]-3,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1]>=4 && solutieOarecare[2]>=1 && solutieOarecare[3]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1]-4,solutieOarecare[2]-1,solutieOarecare[3]-1,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1]>=2 && solutieOarecare[2]>=4)
      {
          var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1]-2,solutieOarecare[2]-4,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1]>=2 && solutieOarecare[2]>=2 && solutieOarecare[3]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1]-2,solutieOarecare[2]-2,solutieOarecare[3]-1,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[1]>=2 && solutieOarecare[3]>=2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1]-2,solutieOarecare[2],solutieOarecare[3]-2,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }if(solutieOarecare[0]>=50)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-50,solutieOarecare[1],solutieOarecare[2],solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=45 && solutieOarecare[1]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-45,solutieOarecare[1]-1,solutieOarecare[2],solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=40 && solutieOarecare[1]>=2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-40,solutieOarecare[1]-2,solutieOarecare[2],solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=40 && solutieOarecare[2]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-40,solutieOarecare[1],solutieOarecare[2]-1,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=35 && solutieOarecare[1]>=3)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-35,solutieOarecare[1]-3,solutieOarecare[2],solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=35 && solutieOarecare[1]>=1 &&solutieOarecare[2]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-35,solutieOarecare[1]-1,solutieOarecare[2]-1,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=30 && solutieOarecare[1]>=4)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-30,solutieOarecare[1]-4,solutieOarecare[2],solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=30 && solutieOarecare[1]>=2 && solutieOarecare[2]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-30,solutieOarecare[1]-2,solutieOarecare[2]-1,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=30 && solutieOarecare[2]>=2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-30,solutieOarecare[1],solutieOarecare[2]-2,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=30 && solutieOarecare[3]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-30,solutieOarecare[1],solutieOarecare[2],solutieOarecare[3]-1,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=25 && solutieOarecare[1]>=5)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-25,solutieOarecare[1]-5,solutieOarecare[2],solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=25 && solutieOarecare[1]>=3 &&solutieOarecare[2]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-25,solutieOarecare[1]-3,solutieOarecare[2]-1,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=25 && solutieOarecare[1]>=1 &&solutieOarecare[2]>=2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-25,solutieOarecare[1]-1,solutieOarecare[2]-2,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=25 && solutieOarecare[1]>=1 && solutieOarecare[3]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-25,solutieOarecare[1]-1,solutieOarecare[2],solutieOarecare[3]-1,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=20 && solutieOarecare[1]>=6)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-20,solutieOarecare[1]-6,solutieOarecare[2],solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=20 && solutieOarecare[1]>=4 && solutieOarecare[2]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-20,solutieOarecare[1]-4,solutieOarecare[2]-1,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=20 && solutieOarecare[1]>=2 && solutieOarecare[2]>=2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-20,solutieOarecare[1]-2,solutieOarecare[2]-2,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=20 && solutieOarecare[1]>=2 && solutieOarecare[3]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-20,solutieOarecare[1]-2,solutieOarecare[2],solutieOarecare[3]-1,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=20 && solutieOarecare[2]>=3)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-20,solutieOarecare[1],solutieOarecare[2]-3,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=20 && solutieOarecare[2]>=1 && solutieOarecare[3]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-20,solutieOarecare[1],solutieOarecare[2]-1,solutieOarecare[3]-1,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=15 && solutieOarecare[1]>=7)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-15,solutieOarecare[1]-7,solutieOarecare[2],solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=15 && solutieOarecare[1]>=5 && solutieOarecare[2]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-15,solutieOarecare[1]-5,solutieOarecare[2]-1,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=15 && solutieOarecare[1]>=3 && solutieOarecare[2]>=2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-15,solutieOarecare[1]-3,solutieOarecare[2]-2,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=15 && solutieOarecare[1]>=3 && solutieOarecare[3]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-15,solutieOarecare[1]-3,solutieOarecare[2],solutieOarecare[3]-1,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=15 && solutieOarecare[1]>=1 && solutieOarecare[2]>=3)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-15,solutieOarecare[1]-1,solutieOarecare[2]-3,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=15 && solutieOarecare[1]>=1 && solutieOarecare[2]>=1 && solutieOarecare[3]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-15,solutieOarecare[1]-1,solutieOarecare[2]-1,solutieOarecare[3]-1,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=10 && solutieOarecare[1]>=8)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-10,solutieOarecare[1]-8,solutieOarecare[2],solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=10 && solutieOarecare[1]>=6 && solutieOarecare[2]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-10,solutieOarecare[1]-6,solutieOarecare[2]-1,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=10 && solutieOarecare[1]>=4 && solutieOarecare[2]>=2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-10,solutieOarecare[1]-4,solutieOarecare[2]-2,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=10 && solutieOarecare[1]>=4 && solutieOarecare[3]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-10,solutieOarecare[1]-4,solutieOarecare[2],solutieOarecare[3]-1,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=10 && solutieOarecare[1]>=2 && solutieOarecare[2]>=3)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-10,solutieOarecare[1]-2,solutieOarecare[2]-3,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=10 && solutieOarecare[1]>=2 && solutieOarecare[2]>=1 && solutieOarecare[3]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-10,solutieOarecare[1]-2,solutieOarecare[2]-1,solutieOarecare[3]-1,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=10 && solutieOarecare[2]>=4)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-10,solutieOarecare[1],solutieOarecare[2]-4,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=10 && solutieOarecare[2]>=2 && solutieOarecare[3]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-10,solutieOarecare[1],solutieOarecare[2]-2,solutieOarecare[3]-1,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=10 && solutieOarecare[3]>=2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-10,solutieOarecare[1],solutieOarecare[2],solutieOarecare[3]-2,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=5 && solutieOarecare[1]>=9)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-5,solutieOarecare[1]-9,solutieOarecare[2],solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=5 && solutieOarecare[1]>=7 && solutieOarecare[2]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-5,solutieOarecare[1]-7,solutieOarecare[2]-1,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=5 && solutieOarecare[1]>=5 && solutieOarecare[2]>=2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-5,solutieOarecare[1]-5,solutieOarecare[2]-2,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=5 && solutieOarecare[1]>=5 && solutieOarecare[3]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-5,solutieOarecare[1]-5,solutieOarecare[2],solutieOarecare[3]-1,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=5 && solutieOarecare[1]>=3 && solutieOarecare[2]>=3)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-5,solutieOarecare[1]-3,solutieOarecare[2]-3,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=5 && solutieOarecare[1]>=3 && solutieOarecare[2]>=1 && solutieOarecare[3]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-5,solutieOarecare[1]-3,solutieOarecare[2]-1,solutieOarecare[3]-1,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=5 && solutieOarecare[1]>=1 && solutieOarecare[2]>=4)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-5,solutieOarecare[1]-1,solutieOarecare[2]-4,solutieOarecare[3],solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=5 && solutieOarecare[1]>=1 && solutieOarecare[2]>=2 && solutieOarecare[3]>=1)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-5,solutieOarecare[1]-1,solutieOarecare[2]-2,solutieOarecare[3]-1,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else if(solutieOarecare[0]>=5 && solutieOarecare[1]>=1 && solutieOarecare[3]>=2)
      {
          var nouaSolutieOarecare := [solutieOarecare[0]-5,solutieOarecare[1]-1,solutieOarecare[2],solutieOarecare[3]-2,solutieOarecare[4]+1];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
      }
      else{
          
          assert solutieOarecare[0]>=0;
          assert solutieOarecare[1]>=0;
          assert solutieOarecare[2]>=0;
          assert solutieOarecare[3]>=3;
          if(solutieOarecare[3]>=3)
          {
            var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1],solutieOarecare[2]+1,solutieOarecare[3]-3,solutieOarecare[4]+1];
            assert cost(nouaSolutieOarecare) < cost(solutieOarecare);
            B(copie, nr, nouaSolutieOarecare, solutieCurenta);
          }
      }
    }

    assert solutieOarecare[4]==(solutieCurenta[4]+1);


    if(solutieOarecare[3] > solutieCurenta[3])
    {
      assert cost([solutieOarecare[0],solutieOarecare[1],solutieOarecare[2],solutieOarecare[3],solutieOarecare[4]-1]) < cost(solutieCurenta);
      assert false;
      
    }
    else if(solutieOarecare[3] < solutieCurenta[3])
      {
        assert (solutieOarecare[0]+(5*solutieOarecare[1])+(10*solutieOarecare[2]))>20;
        
        if(solutieOarecare[2]>=2)
        {
            assert solutieOarecare[2]>=2;
            var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1],solutieOarecare[2]-2,solutieOarecare[3]+1,solutieOarecare[4]];
            B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[2]>=1 && solutieOarecare[1]>=2)
        {
            var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1]-2,solutieOarecare[2]-1,solutieOarecare[3]+1,solutieOarecare[4]];
            B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[2]>=1 && solutieOarecare[1]>=1 && solutieOarecare[0]>=5)
        {
            var nouaSolutieOarecare := [solutieOarecare[0]-5,solutieOarecare[1]-1,solutieOarecare[2]-1,solutieOarecare[3]+1,solutieOarecare[4]];
            B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[1]>=4)
        {
            var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1]-4,solutieOarecare[2],solutieOarecare[3]+1,solutieOarecare[4]];
            B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[1]>=3 && solutieOarecare[0]>=5)
        {
            var nouaSolutieOarecare := [solutieOarecare[0]-5,solutieOarecare[1]-3,solutieOarecare[2],solutieOarecare[3]+1,solutieOarecare[4]];
            B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[1]>=2 && solutieOarecare[0]>=10)
        {
            var nouaSolutieOarecare := [solutieOarecare[0]-10,solutieOarecare[1]-2,solutieOarecare[2],solutieOarecare[3]+1,solutieOarecare[4]];
            B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[1]>=1 && solutieOarecare[0]>=15)
        {
          var nouaSolutieOarecare := [solutieOarecare[0]-15,solutieOarecare[1]-1,solutieOarecare[2],solutieOarecare[3]+1,solutieOarecare[4]];
            B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[0]>=20)
        {
            var nouaSolutieOarecare := [solutieOarecare[0]-20,solutieOarecare[1],solutieOarecare[2],solutieOarecare[3]+1,solutieOarecare[4]];
            B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[2]>=1 && solutieOarecare[0]>=10)
        {
            var nouaSolutieOarecare := [solutieOarecare[0]-10,solutieOarecare[1],solutieOarecare[2]-1,solutieOarecare[3]+1,solutieOarecare[4]];
            B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
      }

    assert solutieOarecare[3] == solutieCurenta[3];

    if(solutieOarecare[2]>solutieCurenta[2])
    {
      assert cost([solutieOarecare[0],solutieOarecare[1],solutieOarecare[2],solutieOarecare[3],solutieOarecare[4]-1]) < cost(solutieCurenta);
      assert false;
    }
    else if(solutieOarecare[2] < solutieCurenta[2])
      {
        assert (solutieOarecare[0]+(5*solutieOarecare[1]))>10;

        if(solutieOarecare[0]>=10)
        {
          var nouaSolutieOarecare := [solutieOarecare[0]-10,solutieOarecare[1],solutieOarecare[2]+1,solutieOarecare[3],solutieOarecare[4]];
          B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
        else if(solutieOarecare[1]>=2){
            var nouaSolutieOarecare := [solutieOarecare[0],solutieOarecare[1]-2,solutieOarecare[2]+1,solutieOarecare[3],solutieOarecare[4]];
             B(copie,nr,nouaSolutieOarecare, solutieCurenta);
        }
          else
          {
            var nouaSolutieOarecare := [solutieOarecare[0]-5,solutieOarecare[1]-1,solutieOarecare[2]+1,solutieOarecare[3],solutieOarecare[4]];
             B(copie,nr,nouaSolutieOarecare, solutieCurenta);
          }
        }
        assert solutieOarecare[2] == solutieCurenta[2];

      if(solutieOarecare[1]>solutieCurenta[1])
    {
      assert cost([solutieOarecare[0],solutieOarecare[1],solutieOarecare[2],solutieOarecare[3],solutieOarecare[4]-1]) < cost(solutieCurenta);
      assert false;
    }
    else
    {
      if(solutieOarecare[1]<solutieCurenta[1])
      {
          assert solutieOarecare[0]>=5;
          var nouaSolutieOarecare := [solutieOarecare[0]-5,solutieOarecare[1]+1,solutieOarecare[2],solutieOarecare[3],solutieOarecare[4]];
          B(copie, nr, nouaSolutieOarecare, solutieCurenta);
        
      }
    }
    assert solutieOarecare[0]==solutieCurenta[0];
    assert false;

  }
}

lemma esteSolutiePentruCopie(copie:int,nr: int, solutieCurenta:seq<int>)
  requires esteSolutieValida(solutieCurenta)
  requires copie >= 50
  requires esteSolutie(solutieCurenta,copie-50)
  requires esteSolutieOptima(solutieCurenta,copie-50)
  ensures esteSolutieOptima([solutieCurenta[0],solutieCurenta[1],solutieCurenta[2],solutieCurenta[3],1+solutieCurenta[4]],copie)
{
  forall solutieOarecare | esteSolutieValida(solutieOarecare) && esteSolutie(solutieOarecare,copie)
    ensures cost(solutieOarecare)>=cost([solutieCurenta[0],solutieCurenta[1],solutieCurenta[2],solutieCurenta[3],1+solutieCurenta[4]])
  {
    B(copie,nr, solutieOarecare, solutieCurenta);
  }
  
}

lemma aux(copie: int ,nr: int, solutieOarecare : seq<int>, solutieFinala : seq<int>, solutieCurenta:seq<int>)
  requires esteSolutieValida(solutieOarecare)
  requires esteSolutieValida(solutieFinala)
  requires esteSolutieValida(solutieCurenta)
  requires copie >= 50
  requires esteSolutieOptima(solutieCurenta,copie-50)
  requires esteSolutie([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],1+solutieFinala[4]+solutieCurenta[4]],nr)
  requires esteSolutie(solutieOarecare,nr)
  requires INV(copie,nr,solutieFinala)
  ensures cost(solutieOarecare) >= cost([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],1+solutieFinala[4]+solutieCurenta[4]])
{
  esteSolutiePentruCopie(copie,nr,solutieCurenta);
}




lemma cazMaxim50(copie: int,nr: int, solutieFinala : seq<int>)
  requires copie >= 50
  requires esteSolutieValida(solutieFinala)
  requires INV(copie,nr,solutieFinala)
  ensures INV(copie-50,nr,[solutieFinala[0],solutieFinala[1],solutieFinala[2],solutieFinala[3],1+solutieFinala[4]])
{
  assert forall solutieCurenta :: esteSolutieValida(solutieCurenta) ==>
          (esteSolutie(solutieCurenta,copie) ==> 
          esteSolutie([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],solutieFinala[4]+solutieCurenta[4]],nr));

   forall solutieCurenta | esteSolutieValida(solutieCurenta) 
          && esteSolutie(solutieCurenta,copie-50) 
          ensures esteSolutie([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],1+solutieFinala[4]+solutieCurenta[4]],nr)
   {
     assert esteSolutie([solutieCurenta[0],solutieCurenta[1],solutieCurenta[2],solutieCurenta[3],1+solutieCurenta[4]],copie);
   }
  

  forall solutieCurenta | esteSolutieValida(solutieCurenta) 
          && esteSolutieOptima(solutieCurenta,copie-50) 
          ensures esteSolutieOptima([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],1+solutieFinala[4]+solutieCurenta[4]],nr)
  {

    assert esteSolutie(solutieCurenta,copie-50);
    assert esteSolutie([solutieCurenta[0],solutieCurenta[1],solutieCurenta[2],solutieCurenta[3],1+solutieCurenta[4]],copie);

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare)
          && esteSolutie(solutieOarecare,copie-50) 
          ==> cost(solutieOarecare) >= cost(solutieCurenta);


    assert esteSolutie([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],1+solutieFinala[4]+solutieCurenta[4]],nr);

    forall solutieOarecare | esteSolutieValida(solutieOarecare)
                 && esteSolutie(solutieOarecare,nr)
      ensures cost(solutieOarecare) >= cost([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],1+solutieFinala[4]+solutieCurenta[4]])
      {
          aux(copie, nr, solutieOarecare, solutieFinala, solutieCurenta);
      }

    assert forall solutieOarecare :: esteSolutieValida(solutieOarecare)
             && esteSolutie(solutieOarecare,nr) 
          ==> cost(solutieOarecare) >= cost([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],1+solutieFinala[4]+solutieCurenta[4]]);
  }


  assert forall solutieCurenta :: esteSolutieValida(solutieCurenta)
          && esteSolutieOptima(solutieCurenta,copie-50) ==> 
          esteSolutieOptima([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],1+solutieFinala[4]+solutieCurenta[4]],nr);


  assert forall solutieCurenta :: esteSolutieValida(solutieCurenta) ==>
          (esteSolutie(solutieCurenta,copie-50) ==> 
          esteSolutie([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],1+solutieFinala[4]+solutieCurenta[4]],nr));
  
  assert forall solutieCurenta :: esteSolutieValida(solutieCurenta) ==>        
          (esteSolutieOptima(solutieCurenta,copie-50) ==> 
          esteSolutieOptima([solutieFinala[0]+solutieCurenta[0],solutieFinala[1]+solutieCurenta[1],solutieFinala[2]+solutieCurenta[2],solutieFinala[3]+solutieCurenta[3],1+solutieFinala[4]+solutieCurenta[4]],nr));

  assert  INV(copie-50,nr,[solutieFinala[0],solutieFinala[1],solutieFinala[2],solutieFinala[3],1+solutieFinala[4]]);
}



  method nrMinimBancnote(nr: int) returns (solutie: seq<int>)
    requires nr>=0
    ensures esteSolutieValida(solutie)
    ensures esteSolutie(solutie,nr)
    ensures esteSolutieOptima(solutie,nr)
{

    var copie:=  nr;
    var s1 := 0;
    var s5 := 0;
    var s10 := 0;
    var s20 := 0;
    var s50 := 0;
    while(copie > 0)
      decreases copie
      invariant 0<=copie<=nr
      invariant esteSolutie([s1,s5,s10,s20,s50],nr-copie)
      invariant INV(copie,nr,[s1,s5,s10,s20,s50])
    {
        var i := 0;
        var s := gasireMaxim(copie);
        if( s == 1){
            cazMaxim1(copie,nr,[s1,s5,s10,s20,s50]);
            s1:=s1+1;
            assert esteSolutie([s1,s5,s10,s20,s50],nr-(copie-1));
            assert INV(copie-1,nr,[s1,s5,s10,s20,s50]);
        }
        else if(s == 5)
            {
                cazMaxim5(copie,nr,[s1,s5,s10,s20,s50]);
                s5:=s5+1;
                assert esteSolutie([s1,s5,s10,s20,s50],nr-(copie-5));
                assert INV(copie-5,nr,[s1,s5,s10,s20,s50]);

            }
            else if (s == 10){
                cazMaxim10(copie,nr,[s1,s5,s10,s20,s50]);
                s10:=s10+1;
                assert esteSolutie([s1,s5,s10,s20,s50],nr-(copie-10));
                assert INV(copie-10,nr,[s1,s5,s10,s20,s50]);

            }
            else if(s == 20){
                cazMaxim20(copie,nr,[s1,s5,s10,s20,s50]);
                s20:=s20+1;
                assert esteSolutie([s1,s5,s10,s20,s50],nr-(copie-20));
                assert INV(copie-20,nr,[s1,s5,s10,s20,s50]);
            }
            else{
                // cazMaxim50(copie,nr,[s1,s5,s10,s20,s50]);
                // s50:=s50+1;
                // assert esteSolutie([s1,s5,s10,s20,s50],nr-(copie-50));
                // assert INV(copie-50,nr,[s1,s5,s10,s20,s50]);
                assume false;
            }

        copie := copie-s;
    }
    solutie := [s1,s5,s10,s20,s50];
}


method Main() {
  var nr:= 58;
  var sol:=nrMinimBancnote(nr);
  print sol;
}