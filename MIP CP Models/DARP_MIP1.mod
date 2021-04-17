execute {
	 cplex.tilim = 600;
 }
int nj= ...;
int nv=...;
int bigM=1000000000; //maxint;  1000000000
range Nodes = 1..nj*2+2; // nj+1 is depot
range Vehicles = 1..nv;
int vCapa=...;

int Dist[Nodes][Nodes];
int Dist_adj[Nodes][Nodes];
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


tuple t_J2J_Travel {
	key int j1;
	key int j2;
	int tt;
};
{t_J2J_Travel} J2J_Travel;

execute { 
for(var i in Jobs)	for(var j in Jobs)
    if(i!=j) J2J_Travel.add(i.id,j.id, Opl.ftoi(Opl.round ( Opl.sqrt( (i.x-j.x)*(i.x-j.x)+(i.y-j.y)*(i.y-j.y))   )));
};

execute { 
for(var j in J2J_Travel)
  Dist[j.j1][j.j2]= j.tt;

for(var j in J2J_Travel)
  if(j.j1==nj*2+1 )  //&& j.j2<=nj*2
    Dist_adj[j.j1][j.j2]= 10000000+ Dist[j.j1][j.j2];//Add 10000 to all D[0,j]
  else
    Dist_adj[j.j1][j.j2]=  Dist[j.j1][j.j2];
};

dvar boolean X[Vehicles][Jobs][Jobs];
dvar int+ B[Vehicles][Jobs];
dvar int+ Q[Vehicles][Jobs];
dexpr float totDistance =
        sum(i,j in Jobs, v in Vehicles) Dist_adj[i.id][j.id] * X[v,i,j];
       	
minimize totDistance/1000;
subject to {
forall (i in Jobs: i.id<=nj)
c2:  	sum(j in Jobs, v in Vehicles) X[v,i,j] ==1;

forall (i,j in Jobs,v in Vehicles: i==j) X[v,i,i] ==0;

forall (v in Vehicles, i in Jobs: i.id<=nj)  	
c3:  	sum(j in Jobs) X[v,i,j]
       == sum(j, ih in Jobs:ih.id==i.id+nj ) X[v,ih,j];

forall (v in Vehicles)  	
c4:  	sum(i,j in Jobs: i.id==2*nj+1) X[v,i,j] == 1; 

forall (v in Vehicles, i in Jobs: i.id<=2*nj)  	
c5:  	sum(j in Jobs) X[v,j,i]
       == sum(j in Jobs) X[v,i,j];
       
forall (v in Vehicles)  	
c6:  	sum(i,j in Jobs: j.id==2*nj+2 ) X[v,i,j] == 1;

forall (i,j in Jobs, v in Vehicles) 
c7:	B[v,j] >= B[v,i]+ Dist[i.id][j.id] - bigM * (1-X[v,i,j]) ;

forall (i,j in Jobs, v in Vehicles) 
c8:		Q[v,j] >= Q[v,i]+j.de - bigM * (1-X[v,i,j]) ;

//pick-up first and drop-off later
forall (v in Vehicles, p,d in Jobs: d.id==p.id+nj && p.id<=nj)
    B[v,p] + Dist[p.id][d.id] <= B[v,d];


forall(i in Jobs,v in Vehicles){
c11:		B[v,i] >= i.est;
c12:		B[v,i] <= i.lst;
}


				
c14:forall (i in Jobs,v in Vehicles) maxl(0,i.de) <= Q[v,i]; 
c15:forall (i in Jobs,v in Vehicles) Q[v,i] <= minl(vCapa,vCapa+i.de); 
	
}

execute {
writeln("v"+"\t" + "i" +"\t" + "j"+"\t"+ "dist" +"\t"+ "est" 
        + "  \t"+ "lst" + "  \t" + "start" +"\t" + "de" +"\t" + "Q");
for (var v in Vehicles) for (var i in Jobs) for (var j in Jobs)
	if ( X[v][i][j]==1)
      	writeln( v +"\t" + i.id  +"\t"+  j.id + "\t" + Dist[i.id][j.id] 
                 + "\t" + j.est + "\t" + j.lst + "\t" + B[v][j] + "\t" +j.de + "\t" +Q[v][j]  ) ;
} 