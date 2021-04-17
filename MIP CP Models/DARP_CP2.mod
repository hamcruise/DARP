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
{t_Job} PJobs = { j | j in Jobs : j.de > 0 };

execute { 
for(var v=2;v<=nv;v++) {
    Jobs.add(nj*2+v*2-1,Jobs.get(nj*2+1).x, Jobs.get(nj*2+1).y, Jobs.get(nj*2+1).st,
		    Jobs.get(nj*2+1).de,Jobs.get(nj*2+1).est, Jobs.get(nj*2+1).lst,0); 
    Jobs.add(nj*2+v*2,Jobs.get(nj*2+2).x, Jobs.get(nj*2+2).y, Jobs.get(nj*2+2).st,
		    Jobs.get(nj*2+2).de,Jobs.get(nj*2+2).est, Jobs.get(nj*2+2).lst,0);
    }		       
//writeln(Jobs);  
};
tuple t_J2J_Travel {
	key int j1;
	key int j2;
	int tt;
};
{t_J2J_Travel} J2J_Travel;
execute { 
for(var i in Jobs)	for(var j in Jobs) {
// if vehicle is full, force to drop off the passenger by imposing bigM on all other pairs. 
//	if(i.id!=j.id-nj && j.id<= nj*2 && vCapa==i.de) J2J_Travel.add(i.id,j.id,99999); //maxDist+100
// if pick(i)+pick(j) >= capa, forbid the trip
//	else if(i!=j && i.id<= nj && j.id<= nj && vCapa < i.de+j.de) J2J_Travel.add(i.id,j.id, 77777);
// if pick(i), forbid trip to depot
//	else if(i!=j && i.id<= nj && j.id> 2*nj) J2J_Travel.add(i.id,j.id, Opl.maxint);
// if all passengers are unloaded, then forbid another drop-off
//	else if(i!=j && (i.id >= nj+1 && i.id <= 2*nj) && (j.id >= nj+1 && j.id <= 2*nj) && vCapa== - i.de) J2J_Travel.add(i.id,j.id, Opl.maxint); //maxDist+100
// if two consecutive tours are all dropoff and dropping off more than the capa, then forbid another drop-off
//	else if(i!=j && (i.id >= nj+1 && i.id <= 2*nj) && (j.id >= nj+1 && j.id <= 2*nj) && vCapa < - i.de- j.de) J2J_Travel.add(i.id,j.id,Opl.maxint); //maxDist+100
	
//    else
   if(i!=j) J2J_Travel.add(i.id,j.id, Opl.ftoi(Opl.round ( Opl.sqrt( (i.x-j.x)*(i.x-j.x)+(i.y-j.y)*(i.y-j.y))   )));
	}
//writeln(J2J_Travel);	
};

execute { 
for(var i in Jobs)	for(var j in Jobs)
  {Dist[i.id][j.id]= Opl.ftoi(Opl.round ( Opl.sqrt( (i.x-j.x)*(i.x-j.x)+(i.y-j.y)*(i.y-j.y))));
//   writeln(i.id +"\t"+ j.id +"\t"+ Dist[i.id][j.id]);
}  
};

//dvar interval bVehicleUsed[Vehicles] optional;

dvar interval itvJob[j in Jobs] size j.st ;
dvar interval itvJ2V[j in Jobs][Vehicles] optional;
dvar interval useCap[j in PJobs];
dvar interval useCapV[j in PJobs][Vehicles] optional;

dvar sequence seqVeh[v in Vehicles] 
 		in 	  all(j in Jobs) itvJ2V[j][v]  
 		types all(j in Jobs) j.id; 	
 			
cumulFunction Loading[v in Vehicles] = 
 	sum(j in PJobs) pulse(useCapV[j][v], j.de);
 	
dexpr int totDistance =
    (sum(j in Jobs, v in Vehicles) Dist[j.id][typeOfNext(seqVeh[v], itvJ2V[j][v], j.id, j.id)]) ;	

//dexpr int cntVehicle = sum( v in Vehicles) bVehicleUsed[v]; 
//dexpr int Makespan  = max(j in Jobs: j.id>nj*2) endOf(itvJob[j])  ; 

execute {
  cp.param.TimeLimit = 10;
  cp.param.Workers = 4;
  cp.param.LogVerbosity=21;  
  cp.param.LogPeriod = 1000000;
 // cp.param.TemporalRelaxation = "On";
  cp.param.NoOverlapInferenceLevel = "Extended"  
  var f = cp.factory;
  cp.setSearchPhases(f.searchPhase(useCapV)); 
}

minimize (10000*nv + totDistance/1000);      
//minimize (totDistance);  
//minimize Makespan;

constraints {
//10000*nv + totDistance/1000 <=31086;


forall(j in Jobs){
    alternative(itvJob[j], all(v in Vehicles) itvJ2V[j][v]);
	startOf(itvJob[j]) >= j.est;
	startOf(itvJob[j]) <= j.lst;
	endOf(itvJob[j]) >= j.est;
} 	
	
forall(j in PJobs) 
	alternative(useCap[j], all(v in Vehicles) useCapV[j][v]);

forall(j,jh in Jobs: j.id==jh.id-nj && jh.id<= nj*2) {
   endBeforeStart(itvJob[j],itvJob[jh], Dist[j.id][jh.id]); //valid constraint
   sizeOf(useCap[j]) >= Dist[j.id][jh.id] + j.st + jh.st;  //valid constraint
   startAtStart(itvJob[j],useCap[j]);
   endAtEnd(itvJob[jh],useCap[j]);
   forall(v in Vehicles) {
     startAtStart(itvJ2V[j][v],useCapV[j][v]);
     endAtEnd(itvJ2V[jh][v],useCapV[j][v]);
     before(seqVeh[v],itvJ2V[j][v],itvJ2V[jh][v]);
   }     
}


forall(v in Vehicles){  	
  noOverlap(seqVeh[v], J2J_Travel);
  Loading[v] <= vCapa;
}

//the same vehicle must be used to destination
forall(v in Vehicles, j,jh in Jobs: j.id==jh.id-nj && jh.id<= nj*2) {
    presenceOf(itvJ2V[j][v])==presenceOf(itvJ2V[jh][v]);
    presenceOf(itvJ2V[j][v])==presenceOf(useCapV[j][v]);
  }    
    
forall(v in Vehicles,j in Jobs: nj*2+v==j.id ){ // Truck stars from depot 
	presenceOf(itvJ2V[j][v])==1;
	first (seqVeh[v],itvJ2V[j][v]); 
}		

forall(v in Vehicles,j in Jobs: nj*2+nv+v==j.id){  // Truck returns to depot at the end
	presenceOf(itvJ2V[j][v])==1;
	last (seqVeh[v],itvJ2V[j][v]);  
}

/*	
// if vehicle is full, force to drop off. 
forall(v in Vehicles,j in Jobs: j.id <= nj && vCapa==j.de)
   typeOfNext(seqVeh[v], itvJ2V[j][v], j.id, j.id+nj) == j.id+nj;
   //	nj < typeOfNext(seqVeh[v], itvJ2V[j][v], j.id, nj+1) <= 2*nj;
  	
// if vehicle is full, the prev job cannot be pickup
forall(v in Vehicles,j in Jobs: j.id <= nj && vCapa==j.de)
  	nj < typeOfPrev(seqVeh[v], itvJ2V[j][v], j.id, nj+1);
  	
// if drop the full load, forbid drop
forall(v in Vehicles,j in Jobs: j.id > nj && j.id <= 2*nj && vCapa==j.de)
  	typeOfNext(seqVeh[v], itvJ2V[j][v], j.id, nj+1) <= nj
  	|| typeOfNext(seqVeh[v], itvJ2V[j][v], j.id, nj+1) > 2*nj ;
*/	    

} 


execute {
// id,type,nd,sz,est,lst,sharing
writeln("v"+"\t" + "i" +"\t" + "q" +"\t" + "est" + "  \t"+ "lst" + "  \t" + "start" );

for (var v in Vehicles)  
for (var j in Jobs) 
	if (  itvJ2V[j][v].present)  //bVehicleUsed[v]==1 &&
      	writeln( v +"\t"+ j.id +"\t"+  j.de +"\t"+ j.est+ "\t" + j.lst +"\t"+  itvJob[j].start ) ;      	
}        