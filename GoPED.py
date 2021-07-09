#-------------------------------------------------TraceMaker--------------------------------------------
# In goal-oriented process mining, this code is for selecting a subset of an event log to infer a process model that
# guarantees a minimum satisfaction level for one or multiple goals for all cases by a predefined confidence level.
# The input of this tool is as follows:
# 1- EnhancedLog: A table of logs whose columns are the satisfaction level of all goals and rows are cases.
# 2- Q_cases: A set of criteria that shows the minimum satisfaction level for some of the goals
# 3- ConfidenceLevel : A confidence level
#-Format of inputs: ------------------------------------------------------------------------------------------------------
# EnhancedLog: a CSV file structured as follows:
# Column 1: Case identifier
# Column 2: Trace
# Column 3,...: Satisfaction level of Goal#1, Goal#2,...
# First row: Column header (The titles are not restricted)
# Second row: the minimum satisfaction level of each goal (at least for one goal).

#--------------------------------------------------------------------------------------------------------

import csv
import os
import time
import re
import argparse
import sys
import docplex.mp
import cplex
from docplex.mp.model import Model

#Inputs---------------------------------------------------------------------------------------------------

myparser=argparse.ArgumentParser(description="This is a line of string that defines all inputs needed to run the algorithms")

#Defining arguments:
myparser.add_argument("-Input", help="The name of the input csv file with .csv")
myparser.add_argument("-Alg", "--Algorithm", help="Algorithm=1,2, or 3, to define the viewpoint")
myparser.add_argument("-GoalCriteria", "--GoalCriteria",nargs="*", help="shows the goal related criteria in the format of G1>=80 G2>=67 G5>90")
myparser.add_argument("-ConfidenceLevel","--ConfidenceLevel", help="to define the Confidence Level for Algorithm 1", )
myparser.add_argument("-Model","--GoalModelFunction", help="to define the function deriven from the goal model, for Algorithm 3", )

myargs=myparser.parse_args()

InputFileName=myargs.Input
AlgorithmNumber=myargs.Algorithm
ConfidenceLevel=myargs.ConfidenceLevel
RawGoalCriteria=myargs.GoalCriteria # this is raw and will be split
GoalModelFunction=myargs.GoalModelFunction

TheInputGoalModelFunction=GoalModelFunction # to keep the original shape of the Goal Model Function

AlgorithmNumber=int(AlgorithmNumber) #that is coming from myargs.

# making the list of goals criteria
if AlgorithmNumber!=3: # as the goal-related criteria in algorithm 3 has the format of Comp>={number} and its format is not like <goal, number, operator, number> like Algorithms 1 and 2
    GoalCriteriaList=[]
    #print(RawGoalCriteria)
    for Goal in RawGoalCriteria:
        CriterionList = re.split('(\d+)', Goal.replace(" ","")) # to remove spaces and then separate the criterion to a list that contains goal, number, operator, number
        CriterionList[3: len(CriterionList)] = [''.join(CriterionList[3: len(CriterionList)])]# to merge the decimal of the number if any to the last cell of the list
        GoalCriteriaList.append(CriterionList)


# Generating set of considered goals------------
    SetOfIndexesOfConsideredGoals = set()
    for Criterion in GoalCriteriaList:
        SetOfIndexesOfConsideredGoals.add(int(Criterion[1]))

if AlgorithmNumber==3:
    CompCriterion=RawGoalCriteria[0]

start_time = time.time()#temp

#The name of the output file:
OutputFileName= "SelectedCases_from_"+InputFileName + time.strftime('@%Y-%m-%dT%H-%M-%S', time.localtime())

# The name of the text file of the output screen:
ScreenOutPutFileName = OutputFileName + '.txt'

# opens the table of EnhancedLog for reading
EnhancedLog=csv.reader(open(InputFileName, "r"))

# constructs a list from the input table
EnhancedLog=list(EnhancedLog)
NumberOfGoalsInEnhancedLog=len(EnhancedLog[0])-2
if AlgorithmNumber!=3:
    if len(EnhancedLog[0][2:])<max(SetOfIndexesOfConsideredGoals):
        print("The index of considered goals are:", SetOfIndexesOfConsideredGoals)
        print("There are", len(EnhancedLog[0][2:]),"goals in the log. Goal", max(SetOfIndexesOfConsideredGoals), "doesn't exist. Please try again.")
        sys.exit()

#Exctacting header of the input file that shows the name of goals
HeaderOfInputFile=EnhancedLog[0]

# To get rid of the header (the first row of the original log)
EnhancedLog=EnhancedLog[1:]

#keep the number of cases
NumberOfCases=len(EnhancedLog)

#initialing SelectedCases used for all algorithms
SelectedCases = set()

#Algorithm1:______________________________________________________
if AlgorithmNumber==1:

    ConfidenceLevel = float(ConfidenceLevel)  # a number in [0-1] as ConfidenceLevel for Alg 1. for example 0.7
    if ConfidenceLevel < 0.0 or ConfidenceLevel > 1.0:
      print("The confidence level must be a number within [0,1], please try again.")
      sys.exit(0)
    # sort the cases based on their traces
    EnhancedLog.sort(key=lambda case: case[1])

    # trace(case_0)←<>  is an empty trace, which cannot happen in reality
    EnhancedLog.insert(0, ["", ""])# To have somthing "" as Trace(Case0) that we will need later, !

    # flag the end of the log: trace(case_NumberOfCases+1)←<> that is an empty trace, which cannot happen in reality
    EnhancedLog.append(["", ""])

    # defining a function to check the satisfaction level of an input case against the criteria and return a True or False that the case satisfying the criteria or not
    def SatisfyingTheGoalCriteria(case):
        condition = True
        for GoalCriterion in GoalCriteriaList:
            if not condition:
                break
            if GoalCriterion[2] == ">=":
                condition = float(case[int(GoalCriterion[1]) - 1]) >= float(GoalCriterion[3])
            elif GoalCriterion[2] == ">":
                condition = float(case[int(GoalCriterion[1]) - 1]) > float(GoalCriterion[3])
            elif GoalCriterion[2] == "<=":
                condition = float(case[int(GoalCriterion[1]) - 1]) <= float(GoalCriterion[3])
            elif GoalCriterion[2] == "<":
                condition = float(case[int(GoalCriterion[1]) - 1]) < float(GoalCriterion[3])
            elif GoalCriterion[2] == "=":
                condition = float(case[int(GoalCriterion[1]) - 1]) == float(GoalCriterion[3])
            elif GoalCriterion[2] in ("!=","<>"):
                condition = float(case[int(GoalCriterion[1]) - 1]) != float(GoalCriterion[3])

            else:
                print(GoalCriterion[2],"is not accepted as a comparison operator! Please try again.")
                sys.exit(0)
        return condition



    NumberOfUniqueTracesInOriginalLog = 0
    NumberOfUniqueTracesInSelectedCases = 0
    index = 1
    while index <= NumberOfCases:
        SameTraceCases = set()  # a set of cases whose traces are the same
        NumberOfSatisfiedCasesOfTrace = 0
        while True:
            SameTraceCases.add(EnhancedLog[index][0])
            if SatisfyingTheGoalCriteria(EnhancedLog[index][2:]):
                NumberOfSatisfiedCasesOfTrace += 1
            index += 1
            if EnhancedLog[index][1] != EnhancedLog[index - 1][1]:
                break
        if NumberOfSatisfiedCasesOfTrace / len(SameTraceCases) >= ConfidenceLevel:
            SelectedCases = SelectedCases.union(SameTraceCases)
            NumberOfUniqueTracesInSelectedCases += 1
        NumberOfUniqueTracesInOriginalLog += 1

#Algorithm2:______________________________________________________
elif AlgorithmNumber==2 :
    #if the solver is on the cloud:"
    #url = "https://api-oaas.docloud.ibmcloud.com/job_manager/rest/v1/"
    #key = "api_83cf2159-f34a-4251-9909-f93b7fa7ad24"
    IndexOfVariables = range(1, NumberOfCases+1)

    # sort the cases based on their traces
    EnhancedLog.sort(key=lambda case: case[1])

    EnhancedLog.insert(0, ["", ""]) #adding one fake line to the begining of EnhancedLog list to map indexex to case numbers

    MyModel = Model(name='GoPED')

    # To create  variables
    # x = MyModel.binary_var_list('x_{0}'.format(i) for i in IndexOfVariables) # Defining the variables in a list instead of a Dic
    x = {i: MyModel.binary_var(name='x_{0}'.format(i)) for i in IndexOfVariables}
    # x=MyModel.binary_var_dict(i for i in IndexOfVariables) some problem, read http://ibmdecisionoptimization.github.io/docplex-doc/mp/docplex.mp.model.html

    # print information of the model:
    # MyModel.print_information()


    # set up constraints:
    NumberOfUniqueTracesInOriginalLog = 0 #this is only a counter for statistics reason
    for i in IndexOfVariables:
        if ( EnhancedLog[i][1] == EnhancedLog[i-1][1]): # if thrace of case i is the same as case i-1
            MyModel.add_constraint(x[i] == x[i-1])  # setting all-or-none rule constraint
        else:
            NumberOfUniqueTracesInOriginalLog +=1 #this is only a counter for statistics reason

    # Alternatively, the two lines below can generate the constraints. Here it is not needed to sort the EnhancedLog
    #for (r, k) in [(r, k) for r in IndexOfVariables for k in IndexOfVariables if (r < k and EnhancedLog[r][1] == EnhancedLog[k][1])]:
        #MyModel.add_constraint(x[r] == x[k]) # all-or-none rule



    for Criterion in GoalCriteriaList: # constraints over the aggregated satisfaction levels
        if Criterion[2]==">=":
            MyModel.add_constraint(MyModel.sum(x[i] * float(EnhancedLog[i][int(Criterion[1])+1]) for i in IndexOfVariables)  >= float(Criterion[3]) * MyModel.sum(x[i] for i in IndexOfVariables) )
        elif Criterion[2]=="<=":
            MyModel.add_constraint(MyModel.sum(x[i] * float(EnhancedLog[i][int(Criterion[1])+1]) for i in IndexOfVariables) <= float(Criterion[3]) * MyModel.sum(x[i] for i in IndexOfVariables) )
        elif Criterion[2] == "=":
            MyModel.add_constraint(MyModel.sum(x[i] * float(EnhancedLog[i][int(Criterion[1]) + 1]) for i in IndexOfVariables) == float(Criterion[3]) * MyModel.sum(x[i] for i in IndexOfVariables))
        else:
            sys.exit("For goal-related criteria of Algorithm 2, only <=,=,>= are allowed. Please try again.  ")



    # define objective
    objective = MyModel.sum(x[i] for i in IndexOfVariables)#Number of selected cases
    # the main goal of the model
    MyModel.maximize(objective) #this is to find the largest subset

    MySolution = MyModel.solve()

    # to assert MySolution # check if the model was solved
    if MySolution:
        # MySolution.display() # or print(MySolution)
        MyObjectiveValue = MySolution.objective_value
        #print("Ojective valu =", MyObjectiveValue)
        #print(MySolution)
        DecisionDic = MySolution.as_dict()
        #print(DecisionDic.keys())
        for i in IndexOfVariables:
            if "x_{0}".format(i) in DecisionDic.keys():
                #print("x_{0}={1}".format(i, int(DecisionDic["x_{0}".format(i)])))
                SelectedCases.add(EnhancedLog[i][0])
            #else:
                #print("x_{0}=0".format(i))
    else:
        print('The model has no feasible answer.')
    #MyModel.export_as_lp(r"E:\Dropbox\UNIVERSITY\Data Paper\tool\Model.lp") #works well to export the model
elif AlgorithmNumber==3:

# parsing the main criterion for for comprehensive satisfaction level to a list
    CompCriterion=CompCriterion.replace(" ","") #Removing all spaces
    if '>=' in CompCriterion:
        CompCriterionList = re.split('(>=)', CompCriterion)
    elif '<=' in CompCriterion:
        CompCriterionList = re.split('(<=)', CompCriterion)
    elif '=' in CompCriterion:
        CompCriterionList = re.split('(=)', CompCriterion)
        CompCriterionList[1]="=="
    else:
        sys.exit("For goal-related criteria of Algorithm 3, only <=,=,>= are allowed. Please try again.")

    IndexOfVariables = range(1, NumberOfCases + 1)

    # sort the cases based on their traces
    EnhancedLog.sort(key=lambda case: case[1])

    EnhancedLog.insert(0, ["",""])  # adding one fake line to the begining of EnhancedLog list to map indexex to case numbers

    MyModel = Model(name='GoPED')

    # Creating  variables:
    # x = MyModel.binary_var_list('x_{0}'.format(i) for i in IndexOfVariables) # Defining the variables in a list instead of a Dic
    x = {i: MyModel.binary_var(name='x_{0}'.format(i)) for i in IndexOfVariables}

    # print information of the model:
    # MyModel.print_information()

    # set up constraints:
    NumberOfUniqueTracesInOriginalLog = 0  # this is only a counter for statistics reason
    for i in IndexOfVariables:
        if (EnhancedLog[i][1] == EnhancedLog[i - 1][1]):  # if thrace of case i is the same as case i-1
            MyModel.add_constraint(x[i] == x[i - 1])  # setting all-or-none rule constraint
        else:
            NumberOfUniqueTracesInOriginalLog += 1  # this is only a counter for statistics reason

    # Alternatively, the two lines below can generate the constraints. Here it is not needed to sort the EnhancedLog:
    # for (r, k) in [(r, k) for r in IndexOfVariables for k in IndexOfVariables if (r < k and EnhancedLog[r][1] == EnhancedLog[k][1])]:
    # MyModel.add_constraint(x[r] == x[k]) # all-or-none rule



#Generating constrians using the GoalModelFunction

    # Replacing all min/max in the input function by MyModel.min/max
    GoalModelFunction= GoalModelFunction.lower() #make sure all characters are in lower case
    GoalModelFunction = GoalModelFunction.replace('min', 'MyModel.min')
    GoalModelFunction = GoalModelFunction.replace('max', 'MyModel.max')

    i=NumberOfGoalsInEnhancedLog
    while i >=1: # replacing all Gi s by sum of all xi.sij. This start from up to down to avoid replacing G10 with the formula of G1
        GoalModelFunction=GoalModelFunction.replace('g' + str(i), 'MyModel.sum(x[i] * float(EnhancedLog[i][' + str(i + 1) + ']) for i in IndexOfVariables)')
        i = i - 1
    # Making a string that shows the complete constraint:
    Constraint='MyModel.add_constraint('+GoalModelFunction+ CompCriterionList[1]+ str(CompCriterionList[2])+'*MyModel.sum(x[i] for i in IndexOfVariables))'
    #converting the string of constraint to a real python code:
    eval(Constraint)

    # To define the objective:
    objective = MyModel.sum(x[i] for i in IndexOfVariables)  # Number of selected cases
    # the main goal of the model:
    MyModel.maximize(objective)  # this is to find the largest subset

    MySolution = MyModel.solve()

    # to assert MySolution # check if the model was solved
    if MySolution:
        # MySolution.display() # or print(MySolution)
        MyObjectiveValue = MySolution.objective_value
        #print("Ojective valu =", MyObjectiveValue)
        #print(MySolution)
        DecisionDic = MySolution.as_dict()
        # print(DecisionDic.keys())
        for i in IndexOfVariables:
            if "x_{0}".format(i) in DecisionDic.keys():
                # print("x_{0}={1}".format(i, int(DecisionDic["x_{0}".format(i)])))
                SelectedCases.add(EnhancedLog[i][0])
            # else:
            # print("x_{0}=0".format(i))
    else:
        print('The model has no feasible answer')

    #MyModel.print_information()
    #print(MyModel)
    MyModel.export_as_lp(r"E:\Dropbox\UNIVERSITY\Data Paper\tool\Model.lp") #works well to export the model

else:
    sys.exit("Algorithm number is wrong.  Please enter 1, 2 or 3.")

#-------------------------------------------------------------------

# Calculation of the execution time
ExecutionTime=time.time() - start_time


#generating the output CSV that contains all selected cases:
SelectedCasesFileName= OutputFileName + '.csv'
SelectedCasesFile = csv.writer(open(SelectedCasesFileName, 'a', newline=''))
caselist=[]
for case in SelectedCases:
    caselist = []
    caselist.append(case)
    SelectedCasesFile.writerow(caselist)

#print(SelectedCases)

#++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

NumberOFPrint=1

while NumberOFPrint<=2 :
    print("=======================================")
    print(time.strftime('%Y-%m-%d  %H:%M:%S', time.localtime()))
    print("file executed:", os.path.basename(sys.argv[0]))
    print("=======================================\n")

    print("Input csv file:", InputFileName, "\n")
    print("Algorithm:", AlgorithmNumber, "\n")

    print("Goal-related Criteria:")
    if AlgorithmNumber == 1:
        print("     Confidence Level=", ConfidenceLevel)

    if AlgorithmNumber != 3:
        print("     Goal criteria: ", end='')
        for y in GoalCriteriaList:
            print(HeaderOfInputFile[int(y[1]) + 1] + y[2] + y[3], '  ', end='')
        print()
        print("     Input goal criteria:", RawGoalCriteria)
        print()
    if AlgorithmNumber == 3:
        print('     Goal model function: G =', TheInputGoalModelFunction)
        print('     The goal Criterion:', CompCriterion)
        print()
    if AlgorithmNumber != 1:
        print("Optimization model:")
        print('     Number of binary variables: {}'.format(MyModel.number_of_binary_variables))
        print('     Number of constraints: {}'.format(MyModel.number_of_constraints))

    print()
    print("Original log: ")
    print("     Number of cases = {}".format(NumberOfCases))
    print("     Number of traces = {}".format(NumberOfUniqueTracesInOriginalLog))
    print()
    print("Output: ")
    print("     Number of selected cases= {}".format(len(SelectedCases)))
    if AlgorithmNumber == 1:
        print("     Number of traces in selected cases=", NumberOfUniqueTracesInSelectedCases)
    print()
    print("The selected cases are stored in", SelectedCasesFileName)
    print("..........................................")

    print("\n\nExecution time: %s seconds" % round(ExecutionTime,5))

    # To show screen out put in a text file**************************************************
    NumberOFPrint = NumberOFPrint + 1
    ScreenOutPutFile = open(ScreenOutPutFileName, 'w')
    sys.stdout = ScreenOutPutFile

