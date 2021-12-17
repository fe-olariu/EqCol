import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;

public class ReadGraphFromFile {

	public ReadGraphFromFile() {
	}

	public static int[] readGraphSize(String dataFile) {
		int[] size = new int[2];
		String path = "../data/EquiCol/", text = null;
		File file = new File(path + "instances/" + dataFile);
		BufferedReader reader = null;
		String[] nors = null;

		try {
			reader = new BufferedReader(new FileReader(file));
			while ((text = reader.readLine()) != null && text.startsWith("c")) {
			}
			if (text.startsWith("p")) {
				nors = text.split("\\s+", 0);
				size[0] = Integer.valueOf(nors[2]);
				size[1] = Integer.valueOf(nors[3]);
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return size;
	}

	public static int readGraph(String dataFile, boolean[][] adjMatrix, int Delta) {
		int[] size = readGraphSize(dataFile);
		int m = size[1], n = size[0], max = 0;
		int[] degrees = new int[n];

		int i, j;
		String path = "../data/EquiCol/", text = null;
		File file = new File(path + "instances/" + dataFile);
		BufferedReader reader = null;
		String[] nors = null;

		try {
			reader = new BufferedReader(new FileReader(file));
			while ((text = reader.readLine()) != null && text.startsWith("c")) {
			}
			for (int k = 0; k < m; k++) {
				if ((text = reader.readLine()) != null && text.startsWith("e")) {
					nors = text.split("\\s+", 0);
					i = Integer.valueOf(nors[1]);
					j = Integer.valueOf(nors[2]);
					adjMatrix[i - 1][j - 1] = true;
					adjMatrix[j - 1][i - 1] = true;
					degrees[i - 1]++;
				}
			}
			for (int k = 0; k < n; k++)
				if (max < degrees[k])
					max = degrees[k];
			Delta = max;

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return max;
	}

	public static void readFile(String dataFile, int Delta) {
		int[] size = readGraphSize(dataFile);
		int n = size[0], m = size[1];
		boolean[][] adj = new boolean[n][n];
		readGraph(dataFile, adj, Delta);
	}

	public static int readGraphK(String dataFile, boolean[][] adjMatrix, int Delta, int k, int p) {
		int[] size = readGraphSize(dataFile);
		int m = size[1], n = size[0], max = 0, i, j;
		int[] degrees = new int[n];
		String path = "../data/EquiCol/", text = null;
		File file = new File(path + "instances/" + dataFile);
		BufferedReader reader = null;
		String[] nors = null;

		try {
			reader = new BufferedReader(new FileReader(file));
			while ((text = reader.readLine()) != null && text.startsWith("c")) {
			}
			for (int h = 0; h < m; h++) {
				if ((text = reader.readLine()) != null && text.startsWith("e")) {
					nors = text.split("\\s+", 0);
					i = Integer.valueOf(nors[1]);
					j = Integer.valueOf(nors[2]);
					adjMatrix[i - 1][j - 1] = true;
					adjMatrix[j - 1][i - 1] = true;
					degrees[i - 1]++;
				}
			}
			if (p > 0) {
				for (int h = 0; h < n; h++)
					for (int l = n; l < n + p; l++) {
						adjMatrix[h][l] = adjMatrix[l][h] = false;
					}
				for (int h = n; h < n + p; h++)
					for (int l = n; l < h; l++)
						adjMatrix[h][l] = adjMatrix[l][h] = true;
			}
			for (int h = 0; h < n; h++)
				if (max < degrees[h])
					max = degrees[h];
			Delta = max;

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return max;
	}

	public static void readFileK(String dataFile, int Delta, int k, int p) {
		int[] size = readGraphSize(dataFile);
		int n = size[0], m = size[1];
		boolean[][] adj = new boolean[n][n];
		readGraphK(dataFile, adj, Delta, k, p);
	}

	public static void main(String[] args) {
		int[] size = readGraphSize("random_100_0.7_1.col");
		int n = size[0], m = size[1], Delta = 0;
		boolean[][] adj = new boolean[n][n];
		readGraph("random_100_0.7_1.col", adj, Delta);
		System.out.println("n = " + n + "; m = " + m);
		System.out.println("End");

	}
}
