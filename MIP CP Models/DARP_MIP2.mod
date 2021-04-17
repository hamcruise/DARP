execute {
	 cplex.tilim = 600;
 }
 int bigM=1000000000; //maxint;  1000000000
 
 
int nj= ...;
int nv=...;

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

int sz[Orders];
execute { 
for(var j in Orders) 
	if(j.de > Limit)
		sz[j]=Opl.ftoi(Opl.round(Opl.sqrt( (j.x-j.dx)*(j.x-j.dx) + (j.y-j.dy)*(j.y-j.dy) )));     
};

int sumSZ = sum (j in Orders) sz[j];

execute { 
for(var i in Orders) for(var j in Orders)
    if(i!=j && i.de > Limit)
       Dist[i.id][j.id]= Opl.ftoi(Opl.round(
       Opl.sqrt( (i.dx-j.x)*(i.dx-j.x) + (i.dy-j.y)*(i.dy-j.y) )));  //drop-loc to pick-loc
   else
       Dist[i.id][j.id]= Opl.ftoi(Opl.round(
	   Opl.sqrt( (i.x-j.x)*(i.x-j.x) + (i.y-j.y)*(i.y-j.y) )));  //drop-loc to pick-loc 	 	

for(var i in Orders) for(var j in Orders)
  if(i.id>=nj*2+1 ) 
    Dist_adj[i.id][j.id]= 10000000+ Dist[i.id][j.id];//Add 10000 to all D[0,j]
  else
    Dist_adj[i.id][j.id]=  Dist[i.id][j.id];
};

dvar boolean X[Vehicles][Orders][Orders];
dvar int+ B[Vehicles][Orders];
dvar int+ Q[Vehicles][Orders];
dexpr float totDistance =
        sum(i,j in Orders, v in Vehicles) Dist_adj[i.id][j.id] * X[v,i,j];
       	
minimize totDistance/1000+sumSZ/1000;
subject to {
forall (i in Orders: i.id<=nj)
c2:  	sum(j in Orders, v in Vehicles) X[v,i,j] ==1;

forall (i,j in Orders,v in Vehicles: i==j) X[v,i,i] ==0;

forall (v in Vehicles, i in Orders: i.id<=nj && i.de <= Limit)  	//not applicable for merged ones
c3:  	sum(j in Orders) X[v,i,j]
       == sum(j, ih in Orders: ih.id==i.id+nj ) X[v,ih,j];

forall (v in Vehicles)  	
c4:  	sum(i,j in Orders: i.id==2*nj+1) X[v,i,j] == 1; 

forall (v in Vehicles, i in Orders: i.id<=2*nj)  	
c5:  	sum(j in Orders) X[v,j,i]
       == sum(j in Orders) X[v,i,j];
       
forall (v in Vehicles)  	
c6:  	sum(i,j in Orders: j.id==2*nj+2 ) X[v,i,j] == 1;

forall (i,j in Orders, v in Vehicles) 
	if  (i.de > Limit) B[v,j] >= B[v,i]+ Dist[i.id][j.id] - bigM * (1-X[v,i,j]) +sz[i]; //if merged ones, then add the merged dist
	else  B[v,j] >= B[v,i]+ Dist[i.id][j.id] - bigM * (1-X[v,i,j]);

forall (i,j in Orders, v in Vehicles) 
 	if (i.de > Limit) Q[v,j] >= Q[v,i]+j.de - bigM * (1-X[v,i,j]) - i.de;
 	else Q[v,j] >= Q[v,i]+j.de - bigM * (1-X[v,i,j]); 	

// if(i!=merged && j==merged) Q[v,j] >= Q[v,i]+j.de - bigM * (1-X[v,i,j])
// if(i!=merged && j!=merged) Q[v,j] >= Q[v,i]+j.de - bigM * (1-X[v,i,j]);


forall(i in Orders,v in Vehicles){ //if merged ones, check out the start-time at drop-off node.
	if  (i.de <= Limit) {
		B[v,i] >= i.est;
		B[v,i] <= i.lst;
	}
	else{
		B[v,i] + sz[i] >= i.dest;
		B[v,i] + sz[i] <= i.dlst;
	}					
}
//pick-up first and drop-off later
forall (v in Vehicles, p,d in Orders: d.id==p.id+nj && p.id<=nj)
    B[v,p] + sz[p] <= B[v,d];

			
forall (i in Orders,v in Vehicles) maxl(0,i.de) <= Q[v,i]; 
forall (i in Orders,v in Vehicles) Q[v,i] <= minl(vCapa,vCapa+i.de); 
	
}

execute {
writeln("v"+"\t" + "i" +"\t" + "j"+"\t"+ "dist" +"\t"+ "est" 
        + "  \t"+ "lst" + "  \t" + "start" +"\t" + "de" +"\t" + "Q"+"\t"+ "dEst" + " \t"+ "dLst");
for (var v in Vehicles) for (var i in Orders) for (var j in Orders)
	if ( X[v][i][j]==1)
      	writeln( v +"\t" + i.id  +"\t"+  j.id + "\t" + Dist[i.id][j.id] 
                 + "\t" + j.est + "\t" + j.lst + "\t" + B[v][j] + "\t" +j.de + "\t" +Q[v][j]  + "\t" + j.dest + "\t" + j.dlst) ;
} 