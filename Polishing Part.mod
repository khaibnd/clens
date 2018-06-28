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
  	}
*/
execute gapTermination {
    cplex.epgap = 0.10; // result at gap of 5%  
 	}  
  
 /**********************Parameters******************/

// Capacity 
int nbspindles = ...;

// Fixed Cost
float backorderCost =...;
float changeCost =...;
float salaryCost =...;
  
//Time
{string} worker = ...;
{int} period = ...;

{string} part = ...;
{string} group = ...;

//Criteria
tuple TCriteria{
	float diameter;
	float ProdStd;
	int spindle;
	string Group;
}
TCriteria partCriteria[part] = ...;
TCriteria groupCriteria[group] = ...;

// Initial Inventory and Back Order
tuple TInitial{
	int iniinventory;
	int inibackorder;
}
TInitial partInitial[part]=...;
TInitial groupInitial[group]=...;

// Worker Skill
tuple TworkerSkill{
	key string worker;
	key string group;
}
{TworkerSkill} workerSkillPart = ...;
float workerSkillPartLevel[workerSkillPart] = ...;

{TworkerSkill} workerSkillGroup = ...;
float workerSkillGroupLevel[workerSkillGroup] = ...;

// Assignment
int step[k in period] = k;
tuple TPartassignment{
	TworkerSkill workerSkillPart;
	int period;
}
{TPartassignment} assignmentPart = {<<w, i>, h> | <w, i> in workerSkillPart, k in period, h in 1..step[k]};

tuple TGroupassignment{
	TworkerSkill workerSkillGroup;
	int period;
}
{TGroupassignment} assignmentGroup = {<<w, i>, h> | <w, i> in workerSkillGroup, k in period, h in 1..step[k]};


// Order and Priority
tuple Torder{
	string group;
	int period;
}

tuple TorderQty{
	int demand;
	int priority;
}
{Torder} orderPart = ...;
TorderQty orderPartQty[orderPart] = ...;

{Torder} orderGroup = ...;
TorderQty orderGroupQty[orderGroup] = ...;


 /**********************Decision Variables**********/

dvar boolean x[assignmentPart] in 0..1;
dvar boolean y[orderPart] in 0..1;

dvar boolean changePart[assignmentPart] in 0..1;

dvar int+ k20[period];

dvar boolean d1[assignmentPart]in 0..1;
dvar boolean d2[assignmentPart]in 0..1;

dvar boolean ua[orderPart] in 0..1;
dvar boolean va[orderPart] in 0..1;

dvar int+ l[workerSkillPart];

dvar int+ spindleuse in 0..3 * nbspindles;

dvar int+ F[orderPart];
dvar int+ J[assignmentPart];

dvar int+ inventory[orderPart];
dvar int+ backorder[orderPart];
dvar int+ production[orderPart];
//int production[i in order]=i.period;

dvar float+ workHr[worker, period] in 0..1;
dexpr float X = sum(<i, h> in orderPart) backorderCost * backorder[<i, h>];
dexpr float Y = sum(<<w, i>, h> in assignmentPart) changeCost * changePart[<<w, i>, h>];
// dexpr float Z = sum(w in worker, h in period) salaryCost * (workHr[w,h] - 7.17);

 /**********************Objective*******************/

minimize X + Y;

 /**********************Constraints*****************/

subject to {

ct1balanceProductionandDemand: // Each period, each part: demand = prod + last Inventory 
						  	   // - last BackOrder - period Inventory + period BackOrder 
	forall (<i, h> in orderPart) {
		if(h == 1){	
	
			orderPartQty[<i, h>].demand == production[<i, h>] /*+ partInitial[i].iniinventory - partInitial[i].inibackorder */- inventory[<i, h>] + backorder[<i, h>];	
		}		
		else {		
			orderPartQty[<i, h>].demand == production[<i, h>] + inventory[<i, h-1>]  - backorder[<i, h-1>] - inventory[<i, h>] + backorder[<i, h>];
 		} 	
	}
	
ct1BackorderandInventoryRelationship: // in each period, have either Back Order or Inventory Balance per part
	forall (<i, h> in orderPart : h >= 2) {
		ua[<i, h>] <= inventory[<i, h>];
		inventory[<i, h>] <= 1000000 * ua[<i, h>];
		
		va[<i, h>] <= backorder[<i, h>];
		backorder[<i, h>] <= 1000000 * ua[<i, h>];
		
		ua[<i, h>] + va[<i, h>] <= 1;
	}

ct2DailyWork: // Daily working hour each worker and its daily output relationship
	forall (w in worker, h in period) {
		sum(<<wc, i>, hc> in assignmentPart: w == wc && h == hc ) x[<<w, i>, h>] <= workHr[w, h];		
	}

ct2aDailyWorkHr: // Constraint working Hour per day limitation
	forall (<<w, i>, h> in assignmentPart) {
		(J[<<w, i>, h>] * partCriteria[i].ProdStd / workerSkillPartLevel[<w, i>]) <= 7.17;
	}

ct3dailyProductionOutput: //Using Big-M to convert  production variable
	forall (<i, h> in orderPart) {
		F[<i, h>] >= production[<i, h>] - 1000000 * (1-y[<i, h>]);
		F[<i, h>] <= production[<i, h>] + 1000000 * (1-y[<i, h>]);		
	}

ct4yconstraint: // 1 if part i is process in period h; =0 otherwise
	forall (<i, h> in orderPart) {
		y[<i, h>] <= production[<i, h>];
		production[<i, h>] <= 1000000 * y[<i, h>];		
	}
	
ct4byconstraint: // 1 if part i is process in period h; =0 otherwise
	forall (<i, h> in orderPart) {
		y[<i, h>] <= F[<i, h>];
		F[<i, h>] <= 1000000 * y[<i, h>];		
	}

ct5dailyProductionOutputperWorker:
	forall(i in part, h in period) {
		sum(<<w, i>, h> in assignmentPart: workerSkillPartLevel[<w, i>] >0) J[<<w, i>, h>] == production[<i, h>];
	}
		
ct6xconstraint: // 1 if part i is process with worker w in period h; =0 otherwise
	forall (<<w, i>, h> in assignmentPart) {
		x[<<w, i>, h>] <= J[<<w, i>, h>];
		J[<<w, i>, h>] <= 1000000*x[<<w, i>, h>];	
	}

ct7xyRelationship: // y = 1 if atleast one x = 1
	forall(<i, h> in orderPart) {
		sum(<<w, i>, h> in assignmentPart) x[<<w, i>, h>]	<= 1000000*  y[<i, h>];
		sum(<<w, i>, h> in assignmentPart) x[<<w, i>, h>]	>= y[<i, h>];
	}

ct8LimitSpindle: // the maximum spindles capacity
	forall (h in period) {
  		20*(sum(<<w, i>, h> in assignmentPart) x[<<w, i>, h>]) <= spindleuse;  		
 	} 
	
ct9spindleArrangement: // total spindle per Part of load kind have to meet requiremnent
	forall (h in period) { //can thay doi
		sum (<<w, i>, h> in assignmentPart) x[<<w, i>, h>]  == 2 * k20[h];		
		}	
		

ct11PartChangeOverPeriodPerWorker: 
	forall (<<w, i>, h> in assignmentPart : h >= 2) {
		0 <= changePart[<<w, i>, h>] - (x[<<w, i>, h-1>] - x[<<w, i>, h>]);
		changePart[<<w, i>, h>] - (x[<<w, i>, h-1>] - x[<<w, i>, h>]) <= 2 * d2[<<w, i>, h>];
			
		0 <= changePart[<<w, i>, h>] - (x[<<w, i>, h>] - x[<<w, i>, h-1>]);
		changePart[<<w, i>, h>] - (x[<<w, i>, h>] - x[<<w, i>, h-1>]) <= 2 * d1[<<w, i>, h>];
			
		d1[<<w, i>, h>] + d2[<<w, i>, h>] == 1;					
	} // Enhance this ct to the current h=0 situation and period h=1


}

 /**********************Output**********************/


tuple productionARR{
	Torder orderPart;
	float Value;
}

{productionARR} outproductionReport = {<<i, h>, production[<i, h>]> | 
									<i, h> in orderPart : production[<i, h>] > 0};

{productionARR} outbackorderReport = {<<i, h>, backorder[<i, h>]> | 
								    <i, h> in orderPart : backorder[<i, h>] > 0};

{productionARR} outinventoryReport = {<<i, h>, inventory[<i, h>]> |
									<i, h> in orderPart : inventory[<i, h>] > 0};

tuple workerScheduleARR{
	TPartassignment assignmentPart;
	float workTime;
	float outputTarget;
}
{workerScheduleARR} outworkerSchedule = {<<<w, i>, h>,workHr[w, h], J[<<w, i>, h>]> |
									 <<w, i>, h> in assignmentPart : J[<<w, i>, h>] > 0 && workHr[w, h] > 0}; 

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