import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Random;
import java.util.Stack;
import gurobi.GRB;
import gurobi.GRBConstr;
import gurobi.GRBEnv;
import gurobi.GRBException;
import gurobi.GRBLinExpr;
import gurobi.GRBModel;
import gurobi.GRBQuadExpr;
import gurobi.GRBVar;
import gurobi.GRB.DoubleAttr;
import gurobi.GRB.DoubleParam;
import gurobi.GRB.StringAttr;

public class X_EqColHeuristic {

	public static int M, n, m, k, k_up, p = 0, Delta;
	public static boolean[][] adjacency;// adjacency matrix

	public static void readFile(String dataFile) {
		ReadGraphFromFile readGfF = new ReadGraphFromFile();
		int[] size = readGfF.readGraphSize(dataFile);
		n = size[0];
		m = size[1];
		System.out.println("File " + dataFile + " n = " + n + " m = " + m);
		adjacency = new boolean[n][n];
		Delta = readGfF.readGraph(dataFile, adjacency, Delta);
		System.out.println("Delta = " + Delta);
	}

	public static void readFileK(String dataFile) {
		ReadGraphFromFile readGfF = new ReadGraphFromFile();
		int[] size = readGfF.readGraphSize(dataFile);
		n = size[0];
		m = size[1];
		int s = n / k;
		p = 0;
		if (s * k < n) {
			s++;
			p = s * k - n;
		}
		System.out.println("File " + dataFile + " n = " + n + " m = " + m);
		adjacency = new boolean[n + p][n + p];
		Delta = readGfF.readGraphK(dataFile, adjacency, Delta, k, p);
	}

	public static void generateGraph(int v, double p, int h) {
		ReadGraphFromFile readGfF = new ReadGraphFromFile();
		// int[] size = readGfF.readGraphSize(dataFile);
		n = v;
		m = 0;
		adjacency = new boolean[n][n];
		Delta = 0;
		int delta = 0;
		String path = "../data/EquiCol/instances/", nume = "random_" + v + "_" + p + "_" + h + ".col";
		for (int i = 0; i < n; i++) {
			delta = 0;
			for (int j = 0; j < i; j++)
				if ((new Random()).nextDouble() < p) {
					adjacency[i][j] = true;
					adjacency[j][i] = true;
					m++;
					delta++;
				}
			if (delta > Delta)
				Delta = delta;
		}
		System.out.println("Delta = " + Delta);
		String lp_sol_fileName = path + "/" + nume;
		File lp_sol_file = new File(lp_sol_fileName);
		BufferedWriter writer = null;
		try {
			if (!lp_sol_file.exists()) {
				lp_sol_file.createNewFile();
			}
			FileWriter fw = new FileWriter(lp_sol_file);
			writer = new BufferedWriter(fw);
			writer.write("c FILE: " + nume);
			writer.newLine();
			// writer.newLine();
			writer.write("c SOURCE: E. F. Olariu (olariu@info.uic.ro");
			writer.newLine();
			// writer.newLine();
			writer.write("c DESCRIPTION: random graph with " + n + " vertices and edge probability " + p);
			// writer.newLine();
			writer.newLine();
			writer.write("p edge " + n + " " + m);
			writer.newLine();
			for (int i = 0; i < n; i++)
				for (int j = i + 1; j < n; j++)
					if (adjacency[i][j]) {
						writer.write("e " + (i + 1) + " " + (j + 1));
						writer.newLine();
					}
		} catch (IOException e) {
			System.out.println("Error code: " + e.getMessage());
		} finally {
			try {
				if (writer != null) {
					writer.close();
				}
			} catch (IOException e) {
			}
		}
	}

	public static void createDir(String path) {
		// Creating a File object
		File file = new File(path);
		// Creating the directory
		boolean bool = file.mkdir();
		if (bool) {
			System.out.println("Results directory created successfully");
		} else {
			System.out.println("Sorry couldn't create results directory/ Maybe already there?");
		}
	}

	public static void printSolution(GRBModel model) throws GRBException {
		GRBVar[] vars = model.getVars();
		GRBVar var;
		String varName;
		int h, k;
		HashSet<Integer> nodes = new HashSet<Integer>();
		model.optimize();
		System.out.println();
		System.out.print("Optimum: " + model.get(DoubleAttr.ObjVal));
		for (int p = 0; p < vars.length; p++) {
			var = vars[p];
			varName = var.get(GRB.StringAttr.VarName);
			h = varName.indexOf('x');
			if (h != -1)
				System.out.println(varName + " = " + var.get(GRB.DoubleAttr.X));
		}
		for (int p = 0; p < vars.length; p++) {
			var = vars[p];
			varName = var.get(GRB.StringAttr.VarName);
			h = varName.indexOf('w');
			if (h != -1)
				System.out.println(varName + " = " + var.get(GRB.DoubleAttr.X));
		}
	}

	public static GRBModel _ILP_OrderModel_M1(GRBModel model, String fileName, double timeLimit)
			throws GRBException {
		// build the initial ILP model for the Equitable Coloring Problem
		// (partial-ordering
		// model)
		System.out.println("Model M1");
		String path = "../data/EquiCol/results/";
		GRBLinExpr expr = new GRBLinExpr(), objFunction = new GRBLinExpr();
		model.set(GRB.IntParam.OutputFlag, 1);

		// createDir(path);
		createDir(path + "/" + fileName);

		// Variables:
		for (int i = 0; i < k_up; i++) {
			for (int j = 0; j < n; j++) {
				model.addVar(0, 1.0, 0.0, GRB.BINARY, "y_" + i + "_" + j);
				model.addVar(0, 1.0, 0.0, GRB.BINARY, "z_" + j + "_" + i);
			}
			model.addVar(0, 1.0, 0.0, GRB.BINARY, "v_" + i);
		}
		model.update();

		// Constraints
		for (int j = 0; j < n; j++) {
			expr = new GRBLinExpr();
			expr.addTerm(1.0, model.getVarByName("z_" + j + "_" + 0));
			model.addConstr(expr, GRB.EQUAL, 0, "C_z_" + j + "_" + 0);
			expr = new GRBLinExpr();
			expr.addTerm(1.0, model.getVarByName("y_" + (k_up - 1) + "_" + j));
			model.addConstr(expr, GRB.EQUAL, 0, "C_y_" + (k_up - 1) + "_" + j);
		}

		for (int i = 0; i < k_up - 1; i++) {
			for (int j = 0; j < n; j++) {
				expr = new GRBLinExpr();
				expr.addTerm(1.0, model.getVarByName("y_" + i + "_" + j));
				expr.addTerm(-1.0, model.getVarByName("y_" + (i + 1) + "_" + j));
				model.addConstr(expr, GRB.GREATER_EQUAL, 0, "C_yy_" + i + "_" + j);
				expr = new GRBLinExpr();
				expr.addTerm(1.0, model.getVarByName("y_" + i + "_" + j));
				expr.addTerm(1.0, model.getVarByName("z_" + j + "_" + (i + 1)));
				model.addConstr(expr, GRB.EQUAL, 1, "C_yz_" + i + "_" + j);
			}
		}

		for (int j = 0; j < n; j++) {
			for (int h = 0; h < j; h++) {
				if (adjacency[j][h])
					for (int i = 0; i < k_up; i++) {
						expr = new GRBLinExpr();
						expr.addTerm(1.0, model.getVarByName("y_" + i + "_" + j));
						expr.addTerm(1.0, model.getVarByName("z_" + j + "_" + i));
						expr.addTerm(1.0, model.getVarByName("y_" + i + "_" + h));
						expr.addTerm(1.0, model.getVarByName("z_" + h + "_" + i));
						model.addConstr(expr, GRB.GREATER_EQUAL, 1, "Adj_" + i + "_" + j + "_" + h);
					}
			}
		}

		for (int i = 1; i < k_up; i++) {
			expr = new GRBLinExpr();
			for (int j = 0; j < n; j++) {
				expr.addTerm(1.0, model.getVarByName("y_" + (i - 1) + "_" + j));
				expr.addTerm(-1.0, model.getVarByName("y_" + i + "_" + j));
				expr.addTerm(1.0, model.getVarByName("y_0_" + j));
			}
			model.addConstr(expr, GRB.LESS_EQUAL, n, "EquitableIncreasing_" + i);
		}
		for (int i = 1; i < k_up; i++) {
			expr = new GRBLinExpr();
			for (int j = 0; j < n; j++) {
				expr.addTerm(1.0, model.getVarByName("y_" + (i - 1) + "_" + j));
				expr.addTerm(-1.0, model.getVarByName("y_" + i + "_" + j));
				expr.addTerm(1.0, model.getVarByName("y_0_" + j));
			}
			expr.addTerm(M, model.getVarByName("v_" + i));
			model.addConstr(expr, GRB.GREATER_EQUAL, n - 1, "EquitableCardinalityGreater_" + i);
		}

		for (int i = 1; i < k_up; i++) {
			expr = new GRBLinExpr();
			for (int j = 0; j < n; j++) {
				expr.addTerm(1.0, model.getVarByName("y_" + (i - 1) + "_" + j));
				expr.addTerm(-1.0, model.getVarByName("y_" + i + "_" + j));
			}
			expr.addTerm(M, model.getVarByName("v_" + i));
			model.addConstr(expr, GRB.LESS_EQUAL, M, "EquitableCardinalityLess_" + i);
		}

		for (int j = 0; j < n; j++) {
			objFunction.addTerm(-1, model.getVarByName("y_0_" + j));
		}
		// Objective function:
		model.setObjective(objFunction);
		model.set(DoubleAttr.ObjCon, n);
		model.set(GRB.IntAttr.ModelSense, GRB.MAXIMIZE);
		model.update();

		// model.write(path + "/" + fileName + "/orderedModel_3.lp");
		model.set(DoubleParam.TimeLimit, timeLimit);
		System.out.println("Optimizing ...");
		model.optimize();
		return model;
	}

	public static GRBModel _ILP_AssignmentModel_M2(GRBModel model, String fileName, double timeLimit)
			throws GRBException {
		// build the initial ILP model for the Equitable Coloring Problem (assignment
		// model)
		System.out.println("Model M2");
		String path = "../data/EquiCol/results/";
		GRBLinExpr expr, expr1, expr2 = new GRBLinExpr(), objFunction = new GRBLinExpr();
		model.set(GRB.IntParam.OutputFlag, 1);

		// createDir(path);
		createDir(path + "/" + fileName);

		// Variables:
		for (int j = 0; j < k_up; j++) {
			for (int i = 0; i < n; i++)
				model.addVar(0, 1.0, 0.0, GRB.BINARY, "x_" + i + "_" + j);
			model.addVar(0, 1.0, 0.0, GRB.BINARY, "w_" + j);
			model.addVar(0, 1.0, 0.0, GRB.BINARY, "v_" + j);
		}
		model.update();
		System.out.println("End - creating variables");

		// Constraints
		for (int j = 0; j < n; j++) {
			expr = new GRBLinExpr();
			for (int i = 0; i < k_up; i++)
				expr.addTerm(1.0, model.getVarByName("x_" + j + "_" + i));
			model.addConstr(expr, GRB.EQUAL, 1, "Coloring_" + j);
		}
		model.update();
		System.out.println("End - creating coloring constraints");

		for (int j = 0; j < n; j++) {
			for (int h = 0; h < j; h++) {
				if (adjacency[j][h])
					for (int i = 0; i < k_up; i++) {
						expr = new GRBLinExpr();
						expr.addTerm(1.0, model.getVarByName("x_" + j + "_" + i));
						expr.addTerm(1.0, model.getVarByName("x_" + h + "_" + i));
						expr.addTerm(-1.0, model.getVarByName("w_" + i));
						model.addConstr(expr, GRB.LESS_EQUAL, 0, "Adj_" + i + "_" + j + "_" + h);
					}
			}
		}
		System.out.println("End - creating adjacency constraints");
		model.update();
		System.out.println("End - creating adjacency constraints + update");
		for (int i = 0; i < k_up - 1; i++) {
			expr = new GRBLinExpr();
			expr.addTerm(1.0, model.getVarByName("w_" + (i + 1)));
			expr.addTerm(-1.0, model.getVarByName("w_" + i));
			model.addConstr(expr, GRB.LESS_EQUAL, 0, "OrderedColors_" + i);
		}
		model.update();
		System.out.println("End - creating ordered colors constraints");

		for (int i = 1; i < k_up; i++) {
			expr = new GRBLinExpr();
			expr1 = new GRBLinExpr();
			expr2 = new GRBLinExpr();
			for (int j = 0; j < n; j++) {
				expr.addTerm(1.0, model.getVarByName("x_" + j + "_" + i));
				expr.addTerm(-1.0, model.getVarByName("x_" + j + "_" + 0));
				expr1.addTerm(1.0, model.getVarByName("x_" + j + "_" + i));
				expr1.addTerm(-1.0, model.getVarByName("x_" + j + "_" + 0));
				expr2.addTerm(1.0, model.getVarByName("x_" + j + "_" + i));
			}
			// first color class is of maximum cardinality (max):
			model.addConstr(expr, GRB.LESS_EQUAL, 0, "EquitableLess_" + i);
			// any non-empty color class has its cardinality at least max - 1:
			expr1.addTerm(M, model.getVarByName("v_" + i));
			model.addConstr(expr1, GRB.GREATER_EQUAL, -1, "EquitableLeast_" + i);
			// a color class may be empty:
			expr2.addTerm(M, model.getVarByName("v_" + i));
			model.addConstr(expr2, GRB.LESS_EQUAL, M, "EquitableEmpty_" + i);
		}
		model.update();
		System.out.println("End - creating equitable cardinality constraints");

		// Objective function:
		for (int j = 0; j < n; j++)
			objFunction.addTerm(1, model.getVarByName("x_" + j + "_0"));

		model.setObjective(objFunction);
		model.set(GRB.IntAttr.ModelSense, GRB.MAXIMIZE);
		System.out.println("End - creating objective function");
		model.update();
		System.out.println("End updating");

		// model.write(path + "/" + fileName + "/assignmentModel.lp");
		model.set(DoubleParam.TimeLimit, timeLimit);
		System.out.println("Optimizing ...");
		model.optimize();
		return model;
	}

	public static GRBModel _ILP_AssignmentModel_M2P(GRBModel model, String fileName, double timeLimit)
			throws GRBException {
		// build the initial ILP model for Equitable Coloring Problem (assignment model)

		System.out.println("Model M2P");
		String path = "../data/EquiCol/results/";
		GRBLinExpr expr, expr1, expr2 = new GRBLinExpr(), objFunction = new GRBLinExpr();
		model.set(GRB.IntParam.OutputFlag, 1);
		int ceil = n / k, floor = n / k;
		if (k * floor != n)
			ceil++;
		System.out.println("floor: " + floor);
		System.out.println("ceil: " + ceil);

		// createDir(path);
		createDir(path + "/" + fileName);

		// Variables:
		for (int j = 0; j < k; j++) {
			for (int i = 0; i < n; i++)
				model.addVar(0, 1.0, 0.0, GRB.BINARY, "x_" + i + "_" + j);
			model.addVar(0, 1.0, 0.0, GRB.BINARY, "w_" + j);
		}
		model.update();

		// Constraints
		for (int j = 0; j < n; j++) {
			expr = new GRBLinExpr();
			for (int i = 0; i < k; i++)
				expr.addTerm(1.0, model.getVarByName("x_" + j + "_" + i));
			model.addConstr(expr, GRB.EQUAL, 1, "Coloring_" + j);
		}

		for (int j = 0; j < n; j++) {
			for (int h = 0; h < j; h++) {
				if (adjacency[j][h])
					for (int i = 0; i < k; i++) {
						expr = new GRBLinExpr();
						expr.addTerm(1.0, model.getVarByName("x_" + j + "_" + i));
						expr.addTerm(1.0, model.getVarByName("x_" + h + "_" + i));
						expr.addTerm(-1.0, model.getVarByName("w_" + i));
						model.addConstr(expr, GRB.LESS_EQUAL, 0, "Adj_" + i + "_" + j + "_" + h);
					}
			}
		}

		for (int i = 0; i < k - 1; i++) {
			expr = new GRBLinExpr();
			expr.addTerm(1.0, model.getVarByName("w_" + (i + 1)));
			expr.addTerm(-1.0, model.getVarByName("w_" + i));
			model.addConstr(expr, GRB.LESS_EQUAL, 0, "OrderedColors_" + i);
		}

		for (int i = 0; i < k; i++) {
			expr1 = new GRBLinExpr();
			expr2 = new GRBLinExpr();
			for (int j = 0; j < n; j++) {
				expr1.addTerm(1.0, model.getVarByName("x_" + j + "_" + i));
				expr2.addTerm(1.0, model.getVarByName("x_" + j + "_" + 1));
			}
			// color classes have cardinality at most ceil(n/p):
			model.addConstr(expr1, GRB.LESS_EQUAL, ceil, "EquitableLess_" + i);
			// color classes have cardinality at least floor(n/p):
			model.addConstr(expr2, GRB.GREATER_EQUAL, floor, "EquitableGreater_" + i);
		}

		// Objective function:
		model.setObjective(objFunction);
		model.set(DoubleAttr.ObjCon, 1.0);
		model.set(GRB.IntAttr.ModelSense, GRB.MINIMIZE);
		model.update();

		// model.write(path + "/" + fileName + "/assignementModelP.lp");
		model.set(DoubleParam.TimeLimit, timeLimit);
		System.out.println("Optimizing ...");
		model.optimize();
		return model;
	}

	public static void main(String[] args) throws GRBException {
		String filename = "R125.5.col";
		long start = System.nanoTime();
		readFile(filename);
		System.out.println("Reading time: " + (System.nanoTime() - start) * 1e-9);
		double timeLimit = 1800;
		GRBEnv env = new GRBEnv();
		GRBModel model = new GRBModel(env);
		/* Step 1: */
		int lowBound = 3, upBound = 36; // Delta + 1;
		M = n / lowBound;// to be changed
		if (M * lowBound != n)
			M++;
		System.out.println("M = " + M);
		k_up = upBound;
		// buildInitialLP_OrderModel_M1(model, filename, timeLimit);
		// buildInitialLP_AssignmentModel_M2(model, filename, timeLimit);
		// printSolution(model);

		/* Step 2: */
		// The value of k must added here:
		k = 25;
		for (int i = 25; i <= 36; i++) {
			k = i;
			System.out.println("k = " + k);
			env = new GRBEnv();
			model = new GRBModel(env); 
			_ILP_AssignmentModel_M2P(model, filename, timeLimit);
		}
	}
}
