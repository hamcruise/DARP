using CP;
int nj= ...;
int nv=...; //3; 
//int nv=3; //3; //4; 
range Nodes = 1..nj*2+nv*2; 
range Vehicles = 1..nv;
int vCapa=...;

int Dist[Nodes][Nodes];

tuple t_Job {
key int id;
	int x;
	int y; 
    int st;
    int de;
    int est;
    int lst; 
    int nArr;       
};
{t_Job} Jobs = ...;

int Limit =vCapa - min (j in Jobs: j.de >0) j.de;


tuple t_New {
key int id; 
    int x; 	int y;    int de;    int est; int lst; int dx; int dy;  int dest; int dlst;
  };  //merge pickup and drop into one row if full load
{t_New} Order1 = { <j.id, j.x, j.y, j.de, j.est, j.lst, jh.x, jh.y,jh.est, jh.lst > | j,jh in Jobs: 
                 j.id==jh.id-nj && jh.id<= nj*2 && j.de > Limit && jh.de != 0 };
                 
{t_New} Order2 = { <j.id, j.x, j.y, j.de, j.est, j.lst, 0, 0,0, 0 > | j in Jobs : 
                j.de <= Limit && j.de >= -Limit};

{t_New} Orders = Order1 union Order2;      
{t_New} PJobs = { j | j in Orders : j.de > 0 };
                             

execute { 
for(var v=2;v<=nv;v++) {
    Orders.add(nj*2+v*2-1,Jobs.get(nj*2+1).x, Jobs.get(nj*2+1).y,0,
		    Jobs.get(nj*2+1).est, Jobs.get(nj*2+1).lst,0,0,0,0); 
    Orders.add(nj*2+v*2,Jobs.get(nj*2+2).x, Jobs.get(nj*2+2).y,0,
		    Jobs.get(nj*2+2).est, Jobs.get(nj*2+2).lst,0,0,0,0);
    }		       
//writeln(Orders);  
};
int sz[Orders];
execute { 
for(var j in Orders) 
	if(j.de > Limit)
		sz[j]=Opl.ftoi(Opl.round(Opl.sqrt( (j.x-j.dx)*(j.x-j.dx) + (j.y-j.dy)*(j.y-j.dy) )));     
};

int sumSZ = sum (j in Orders) sz[j];

tuple t_J2J_Travel {
	key int j1;
	key int j2;
	int tt;
};
{t_J2J_Travel} J2J_Travel;
execute { 
for(var i in Orders) for(var j in Orders) 
   if(i!=j && i.de > Limit )
       J2J_Travel.add(i.id,j.id,Opl.ftoi(Opl.round(
       Opl.sqrt( (i.dx-j.x)*(i.dx-j.x) + (i.dy-j.y)*(i.dy-j.y) ))));  //drop-loc to pick-loc
   else
       J2J_Travel.add(i.id,j.id,Opl.ftoi(Opl.round(
	   Opl.sqrt( (i.x-j.x)*(i.x-j.x) + (i.y-j.y)*(i.y-j.y) ))));  //drop-loc to pick-loc
   	 			  			
//writeln(J2J_Travel);      
};
execute { 
for(var i in Orders)	for(var j in Orders)
    if(i!=j && i.de > Limit)
       Dist[i.id][j.id]= Opl.ftoi(Opl.round(
       Opl.sqrt( (i.dx-j.x)*(i.dx-j.x) + (i.dy-j.y)*(i.dy-j.y) )));  //drop-loc to pick-loc
   else
       Dist[i.id][j.id]= Opl.ftoi(Opl.round(
	   Opl.sqrt( (i.x-j.x)*(i.x-j.x) + (i.y-j.y)*(i.y-j.y) )));  //drop-loc to pick-loc
   	 	
};

//dvar interval bVehicleUsed[Vehicles] optional;

dvar interval itvJob[j in Orders] size sz[j];
dvar interval itvJ2V[j in Orders][Vehicles] optional;
dvar interval useCap[j in PJobs];
dvar interval useCapV[j in PJobs][Vehicles] optional;

dvar sequence seqVeh[v in Vehicles] 
 		in 	  all(j in Orders) itvJ2V[j][v]  
 		types all(j in Orders) j.id; 	
 			
cumulFunction Loading[v in Vehicles] = 
 	sum(j in PJobs) pulse(useCapV[j][v], j.de);
 	
dexpr int totDistance =
    (sum(j in Orders, v in Vehicles) Dist[j.id][typeOfNext(seqVeh[v], itvJ2V[j][v], j.id, j.id)]) ;	

//dexpr int cntVehicle = sum( v in Vehicles) bVehicleUsed[v]; 
//dexpr int Makespan  = max(j in Jobs: j.id>nj*2) endOf(itvJob[j])  ; 

execute {
  cp.param.TimeLimit = 30;
  cp.param.Workers = 4;
  cp.param.LogVerbosity=21;  
  cp.param.LogPeriod = 1000000;
  cp.param.TemporalRelaxation = "On";
  cp.param.NoOverlapInferenceLevel = "Extended"  
  var f = cp.factory;
  cp.setSearchPhases(f.searchPhase(useCapV)); 
}

minimize (10000*nv + (sumSZ+totDistance)/1000);      
//minimize (totDistance);  
//minimize Makespan;

constraints {
//10000*nv + totDistance/1000 <=31086;


forall(j in Orders){
    alternative(itvJob[j], all(v in Vehicles) itvJ2V[j][v]);
	startOf(itvJob[j]) >= j.est;
	startOf(itvJob[j]) <= j.lst;
	if(j.de > Limit) {
		endOf(itvJob[j]) >= j.dest;
		endOf(itvJob[j]) <= j.dlst;
	}	
} 	
	
forall(j in PJobs) 
	alternative(useCap[j], all(v in Vehicles) useCapV[j][v]);

forall(j,jh in Orders: j.id==jh.id-nj && jh.id<= nj*2 && j.de <= Limit ) { ///j.de!=vCapa
   endBeforeStart(itvJob[j],itvJob[jh], Dist[j.id][jh.id]); //valid constraint
   sizeOf(useCap[j]) >= Dist[j.id][jh.id];  //valid constraint
   startAtStart(itvJob[j],useCap[j]);
   endAtEnd(itvJob[jh],useCap[j]);
   forall(v in Vehicles) {
     startAtStart(itvJ2V[j][v],useCapV[j][v]);
     endAtEnd(itvJ2V[jh][v],useCapV[j][v]);
     before(seqVeh[v],itvJ2V[j][v],itvJ2V[jh][v]);
   }     
}
///*
forall(j in Orders: j.id<= nj && j.de>Limit) {
   startAtStart(itvJob[j],useCap[j]);
  // endOf(useCap[j])==startOf(itvJob[j])+sz[j]; 
   endAtEnd(itvJob[j],useCap[j]);
   forall(v in Vehicles) {
     startAtStart(itvJ2V[j][v],useCapV[j][v]);
     endAtEnd(itvJ2V[j][v],useCapV[j][v]);     
   //  endOf(useCapV[j][v])==startOf(itvJ2V[j][v])+sz[j];  
   }     
}
//*/
forall(v in Vehicles){  	
  noOverlap(seqVeh[v], J2J_Travel);
  Loading[v] <= vCapa;
//  sum(j in Orders) presenceOf(itvJ2V[j][v])*j.de <=vCapa; //valid constraint
}

//the same vehicle must be used to destination
forall(v in Vehicles, j,jh in Orders: j.id==jh.id-nj && jh.id<= nj*2 && j.de <= Limit) {   
    presenceOf(itvJ2V[j][v])==presenceOf(itvJ2V[jh][v]);
    presenceOf(itvJ2V[j][v])==presenceOf(useCapV[j][v]);
  }    
forall(v in Vehicles, j in Orders: j.id<= nj && j.de > Limit)  //j.de==vCapa
    presenceOf(itvJ2V[j][v])==presenceOf(useCapV[j][v]); 
      
forall(v in Vehicles,j in Orders: nj*2+v==j.id ){ // Truck stars from depot 
	presenceOf(itvJ2V[j][v])==1;
	first (seqVeh[v],itvJ2V[j][v]); 
}		

forall(v in Vehicles,j in Orders: nj*2+nv+v==j.id){  // Truck returns to depot at the end
	presenceOf(itvJ2V[j][v])==1;
	last (seqVeh[v],itvJ2V[j][v]);  
}


// if vehicle is full, force to drop off. 
//forall(v in Vehicles,j in Orders: j.id <= nj && vCapa==j.de)
 //  typeOfNext(seqVeh[v], itvJ2V[j][v], j.id, j.id+nj) == j.id+nj;
   //	nj < typeOfNext(seqVeh[v], itvJ2V[j][v], j.id, nj+1) <= 2*nj;
  	
// if vehicle is full, the prev job cannot be pickup
//forall(v in Vehicles,j in Orders: j.id <= nj && j.de > Limit)
//  	nj < typeOfPrev(seqVeh[v], itvJ2V[j][v], j.id, nj+1);
  	
// if drop the full load, forbid drop
//forall(v in Vehicles,j in Orders: j.id > nj && j.id <= 2*nj && vCapa==j.de)
//  	typeOfNext(seqVeh[v], itvJ2V[j][v], j.id, nj+1) <= nj
//  	|| typeOfNext(seqVeh[v], itvJ2V[j][v], j.id, nj+1) > 2*nj ;
    

} 


execute {
// id,type,nd,sz,est,lst,sharing
writeln("v"+"\t" + "i" +"\t" + "q" +"\t" + "est" + "  \t"+ "lst" + "  \t" + "start" + "  \t" + "end");

for (var v in Vehicles)  
for (var j in Orders) 
	if (  itvJ2V[j][v].present)  //bVehicleUsed[v]==1 &&
      	writeln( v +"\t"+ j.id +"\t"+  j.de +"\t"+ j.est+ "\t" + j.lst +"\t"+  itvJob[j].start  +"\t"+  itvJob[j].end +"\t"+ j.dest+ "\t" + j.dlst +"\t") ;      	
}        