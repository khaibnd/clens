/*********************************************
 * Polishing Production Loading
 * Author: Duy Khai
 * Creation Date: 20-04-2018 at 22:28:38
 + Objective: Minimize Cost of Back Order + Change Job + Overtime Requirement.
 + 
 + Problems:
 + Determine change part variable throw periods
 + Build Overtime model, currently not correct
 + Make the model smoothly
 + Constraint machine setup of movement
 
 
 *********************************************/

/*
execute timeTermination {
  	cplex.tilim = 3*60;   // set time model stop (second)
	}
/*execute setCoefficient {
    cplex.coeredind = 2; //Reduce all potential coefficients
  	} */
execute gapTermination {
    cplex.epgap = 0.05; // result at gap of 5%  
 	}  
  
 /**********************Parameters******************/
  
//Time
{int} worker = ...;
{int} part = ...;
{int} period = ...;

// Worker
tuple TworkerSkill{
	key int worker;
	key int part;
}
{TworkerSkill} workerSkill = ...;

tuple Tassignment{
	TworkerSkill workerSkill;
	int period;
}
int step[k in period] = k;
{Tassignment} assignment = {<<w, i>, h> | <w, i> in workerSkill, k in period, h in 1..step[k]};

// Skill Lever
float workerSkillLever[workerSkill] = ...;

// Part Criteria
tuple TpartCriteria{
	float diameter;
	float ProdStd;
	int spindle;
	string Group;
}
TpartCriteria partCriteria[part] = ...;

// Part Onhand Inventory and Back Order at period h = 1
tuple TpartInitial{
	int iniinventory;
	int inibackorder;
}
TpartInitial partInitial[part]=...;

// Order and Priority
tuple Torder{
	int part;
	int period;
}
{Torder} order = {<i, h> | i in part, k in period, h in 1..step[k]};

tuple TorderARR{
	int demand;
	int priority;
}
TorderARR orderQty[<i, h> in order] = ...;

// Capacity 
int nbspindles = ...;
{string} partGroup=...;

// Fixed Cost
float backorderCost =...;
float changeCost =...;
float salaryCost =...;

 /**********************Decision Variables**********/

dvar boolean x[<<w, i>, h> in assignment] in 0..1;
dvar boolean y[<i, h> in order] in 0..1;

dvar boolean changePart[<<w, i>, h> in assignment] in 0..1;

dvar boolean d1[<<w, i>, h> in assignment]in 0..1;
dvar boolean d2[<<w, i>, h> in assignment]in 0..1;

dvar boolean ua[<i, h> in order] in 0..1;
dvar boolean va[<i, h> in order] in 0..1;

dvar int+ k15[partGroup, period];
dvar int+ k20[partGroup, period];
dvar int+ l[<w, i> in workerSkill];

dvar int+ spindleuse[period] in 0..3 * nbspindles;

dvar int+ F[<i, h> in order];
dvar int+ J[<<w, i>, h> in assignment];

dvar int+ inventory[<i, h> in order];
dvar int+ backorder[<i, h> in order];
dvar int+ production[<i, h> in order];

dvar float+ workHr[worker, period] in 0..7.17;

dexpr float X = sum(<i, h> in order) backorderCost * backorder[<i, h>];
dexpr float Y = sum(<<w, i>, h> in assignment) changeCost * changePart[<<w, i>, h>];
// dexpr float Z = sum(w in worker, h in period) salaryCost*(workHr[w,h] - 7.17);

 /**********************Objective*******************/

minimize X + Y;

 /**********************Constraints*****************/

subject to {

ct1balanceProductionandDemand: // Each period, each part: demand = prod + last Inventory 
						  // - last BackOrder - period Inventory + period BackOrder 
	forall (<i, h> in order) {
		if(h == 1){	
	
			orderQty[<i, h>].demand == production[<i, h>] + partInitial[i].iniinventory - partInitial[i].inibackorder - inventory[<i, h>] + backorder[<i, h>];	
		}		
		else {		
			orderQty[<i, h>].demand == production[<i, h>] + inventory[<i, h-1>]  - backorder[<i, h-1>] - inventory[<i, h>] + backorder[<i, h>];
 		} 	
	}
ct1BackorderandInventoryRelationship: // in each period, have either Back Order or Inventory Balance per part
	forall (<i, h> in order : h >=2) {
		ua[<i, h>] <= inventory[<i, h>];
		inventory[<i, h>] <= 1000000*ua[<i, h>];
		
		va[<i, h>] <= backorder[<i, h>];
		backorder[<i, h>] <= 1000000*ua[<i, h>];
		
		ua[<i, h>] + va[<i, h>] <=1;
	}

ct2DailyWork: // Daily working hour each worker and its daily output relationship
	forall (w in worker, h in period) {
		sum(<<w, i>, h> in assignment)x[<<w, i>, h>] <=1;
	}
	
ct2aDailyWorkHr: // Constraint working Hour per day limitation
	forall (w in worker, h in period) {
		sum(<<w, i>, h> in assignment) (J[<<w, i>, h>]*(partCriteria[i].ProdStd)/workerSkillLever[<w, i>]) 
										== workHr[w,h];
	}

ct3dailyProductionOutput: //Using Big-M to convert  production variable
	forall (<i, h> in order){
		F[<i, h>] >= production[<i, h>] - 1000000*(1-y[<i, h>]);
		F[<i, h>] <= production[<i, h>] + 1000000*(1-y[<i, h>]);		
	}

ct4yconstraint: // 1 if part i is process in period h; =0 otherwise
	forall (<i, h> in order){
		y[<i, h>] <= production[<i, h>];
		production[<i, h>] <= 1000000*y[<i, h>];		
	}
	
ct4byconstraint: // 1 if part i is process in period h; =0 otherwise
	forall (<i, h> in order){
		y[<i, h>] <= F[<i, h>];
		F[<i, h>] <= 1000000*y[<i, h>];		
	}
	
ct5dailyProductionOutputperWorker:
	forall(<i, h> in order){
		sum(<<w, i>, h> in assignment)J[<<w, i>, h>] == production[<i, h>];
	}
	
/*ct6xconstraint: // 1 if part i is process with worker w in period h; =0 otherwise
	forall (<<w, i>, h> in assignment){
		x[<<w, i>, h>] <= J[<<w, i>, h>];
		J[<<w, i>, h>] <= 1000000*x[<<w, i>, h>];	
	}
*/	
ct7xyRelationship: //y = 1 if atleast one x = 1
	forall(i in part, h in period){
		sum(<<w, i>, h> in assignment) x[<<w, i>, h>]	<= 1000000*y[<i, h>];
		sum(<<w, i>, h> in assignment) x[<<w, i>, h>]	>= y[<i, h>];
	}

ct8LimitSpindle: // the maximum spindles capacity
	forall (h in period) {
  		15*(sum(<<w, i>, h> in assignment: partCriteria[i].spindle == 15) x[<<w, i>, h>]) 
  		+ 20*(sum(<<w, i>, h> in assignment: partCriteria[i].spindle == 20) x[<<w, i>, h>]) <= spindleuse[h];  		
 	} 

ct9spindleArrangement: // total spindle per group of load kind have to meet requiremnent
	forall (h in period, g in partGroup){
		sum (<<w, i>, h> in assignment: partCriteria[i].Group == g )x[<<w, i>, h>]*15 == 60*k15[g, h];
		sum (<<w, i>, h> in assignment: partCriteria[i].Group == g )x[<<w, i>, h>]*20 == 40*k20[g, h];		
		}	
		
ct10workerMustCompleteLotSize: // worker have to finish the specific part lot size, 400 or 500pcs/lot
	forall (<w, i> in workerSkill) {
			sum(<<w, i>, h> in assignment: partCriteria[i].spindle == 15)J[<<w, i>, h>] ==400*l[<w, i>];
			sum(<<w, i>, h> in assignment: partCriteria[i].spindle == 20)J[<<w, i>, h>] ==500*l[<w, i>];			
	}
	
ct11PartChangeOverPeriodPerWorker: // 1 if worker w change part from period h-1 to period h; =0 otherwise
	forall (<<w, i>, h> in assignment:h>=2){
		0 <= changePart[<<w, i>, h>] - (x[<<w, i>, h-1>] - x[<<w, i>, h>]);
		changePart[<<w, i>, h>] - (x[<<w, i>, h-1>] - x[<<w, i>, h>]) <= 2*d2[<<w, i>, h>];
			
		0 <= changePart[<<w, i>, h>] - (x[<<w, i>, h>] - x[<<w, i>, h-1>]);
		changePart[<<w, i>, h>] - (x[<<w, i>, h>] - x[<<w, i>, h-1>]) <= 2*d1[<<w, i>, h>];
			
		d1[<<w, i>, h>] + d2[<<w, i>, h>] == 1;					
	} //Enhance this ct to the current h=0 situation and period h=1

}

 /**********************Output**********************/


tuple productionARR{
	Torder order;
	float Value;
}

{productionARR} productionReport = {<<i, h>, production[<i, h>]> | 
									<i, h> in order : production[<i, h>] > 0};

{productionARR} backorderReport = {<<i, h>, backorder[<i, h>]> | 
								    <i, h> in order : backorder[<i, h>] > 0};

{productionARR} inventoryReport = {<<i, h>, inventory[<i, h>]> |
									<i, h> in order : inventory[<i, h>] > 0};

tuple workerScheduleARR{
	Tassignment assignment;
	float workHrperDay;
	float outputTarget;
}
{workerScheduleARR} workerScheduleReport = {<<<w, i>, h>, workHr[w,h], J[<<w, i>, h>]> |
									 <<w, i>, h> in assignment : J[<<w, i>, h>] > 0}; 

/*
 main {
  thisOplModel.generate();
  cplex.solve();
  var ofile = new IloOplOutputFile("modelRun.txt");
  ofile.writeln(thisOplModel.printExternalData());
  ofile.writeln(thisOplModel.printInternalData());
  ofile.writeln(thisOplModel.printSolution());
  ofile.close();
	}
*/