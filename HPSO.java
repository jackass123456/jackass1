package TFSCompared;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.Random;

import common.FJSPSolution;
import common.Operation;
import common.PairData;
import common.ShopData;
import common.TestLocalSearch;
import common.TimeInterval;

public class HPSO {
	int NP;
	int NI;
	int ND;

	double w;
	double c1;
	double c2;
	double Pl;
	double delta;

	double F;
	double Cr;

	int localIterTimes;
	double[] lowerBound;
	double[] upBound;

	Random ran = new Random();

	double[][] v0;
	double[][] v1;
	double[][] G0; // current
	double[][] G1; // temporary
	double[][] G2; // personal

	double[] gBest;

	int[] solVal;

	int bestSolIndex;
	int bestSolVal;
	int hisBestSolVal;

	void initializeParameters() {
		NP = 30; // popSize
		NI = 200; // iteration

		ND = ShopData.getTotalOpNum() * 2; // dimension

		c1 = 1.57;
		c2 = 1.57;
		w = 0.1;
		delta = 1;

		solVal = new int[NP]; // makespan

		Pl = 0.7;
		localIterTimes = 80;

		lowerBound = new double[ND];
		upBound = new double[ND];

		G0 = new double[NP][]; // current
		G1 = new double[NP][]; // intermediate value
		G2 = new double[NP][]; // personal
		v0 = new double[NP][]; // velocity
		v1 = new double[NP][]; // velocity

		gBest = new double[ND];

		int i;

		for (i = 0; i < NP; i++) {
			G0[i] = new double[ND];
			G1[i] = new double[ND];
			G2[i] = new double[ND];
			v0[i] = new double[ND];
			v1[i] = new double[ND];
		}

		for (i = 0; i < ND; i++) {
			lowerBound[i] = -delta;
			upBound[i] = delta;
		}
	}

	void initializePopulation() {
		int i, j;
		for (i = 0; i < NP; i++) {
			for (j = 0; j < ND; j++) {
				G0[i][j] = lowerBound[j] + (upBound[j] - lowerBound[j]) * ran.nextDouble();
				v0[i][j] = lowerBound[j] + (upBound[j] - lowerBound[j]) * ran.nextDouble();
			}
		}

		bestSolVal = Integer.MAX_VALUE;
		bestSolIndex = -1;

		for (i = 0; i < NP; i++) {
			solVal[i] = getFunctionVal(G0[i], ND);
			if (solVal[i] < bestSolVal) {
				bestSolVal = solVal[i];
				bestSolIndex = i;
			}
		}
		G2 = G0.clone();
		gBest = G0[bestSolIndex].clone();
		hisBestSolVal = bestSolVal;
	}

	int getFunctionVal(double vector[], int N) {
		int i;
		int[] temp = convertVectorToPermutation(vector, N);
		int[] code = convertPermutationToCode(temp, N);
		int[] perm = convertCodeToPermutation(code, N);
		int val = decodingPermutation(perm, N);
		ArrayList<Double> tList = new ArrayList<Double>();

		for (i = N / 2; i < N; i++)
			tList.add(vector[i]);
		Collections.sort(tList);
		for (i = N / 2; i < N; i++)
			vector[perm[i] + N / 2 - 1] = tList.get(N - 1 - i);
		return val;
	}

	int[] convertVectorToPermutation(double vector[], int N) {
		ArrayList<PairData> tList = new ArrayList<PairData>();
		int i;
		for (i = N / 2; i < N; i++)
			tList.add(new PairData(i - N / 2 + 1, vector[i]));
		Collections.sort(tList);
		for (i = 0; i < N / 2; i++)
			vector[tList.get(i).getId() + N / 2 - 1] = tList.get(i).getVal();

		int[] result = new int[N];

		for (i = 0; i < N / 2; i++)
			result[i] = (int) Math.round(linearMapping(vector[i], 1, ShopData.getOptionalMachineNum(i + 1)));

		for (i = N / 2; i < N; i++)
			result[i] = tList.get(N - 1 - i).getId();

		return result;
	}

	int[] convertPermutationToCode(int[] permutation, int N) {
		int[] result = new int[N];
		int i;
		for (i = 0; i < N / 2; i++)
			result[i] = permutation[i];
		for (i = N / 2; i < N; i++) {
			int jobId = ShopData.getOpById(permutation[i]).jobId;
			result[i] = jobId;
		}
		return result;
	}

	double linearMapping(double x, int down, int up) {
		return down + (double) ((up - down) * (x + delta)) / (2 * delta);
	}

	double inverseLinearMapping(int y, int down, int up) {
		if (down != up) {
			return (double) (2 * delta * (y - down)) / (up - down) - delta;
		} else
			return -delta + 2 * delta * ran.nextDouble();
	}

	public int[] getBestPerm() {
		int[] bestPerm = convertVectorToPermutation(G0[bestSolIndex], ND);
		return bestPerm;
	}

	int[] convertCodeToPermutation(int[] code, int N) {
		int[] temp = new int[N];
		int[] count = new int[ShopData.getJobNum()];
		int i;
		for (i = 0; i < N / 2; i++)
			temp[i] = code[i];

		for (i = N / 2; i < N; i++) {
			int jobId = code[i];
			int procedureId = ++count[jobId - 1];
			int opID = ShopData.getIdByOp(new Operation(jobId, procedureId));
			temp[i] = opID;
		}
		return temp;
	}

	int decodingPermutation(int[] permutation, int N) {
		int[] curEndTimeOfJob = new int[ShopData.getJobNum()];
		int[] curEndTimeOfMachine = new int[ShopData.getMachineNum()];
		ArrayList<PairData> startTimeInfo = new ArrayList<PairData>();
		ArrayList<LinkedList<TimeInterval>> intervalList = new ArrayList<LinkedList<TimeInterval>>(
				ShopData.getMachineNum());
		int i, j, max;
		for (i = 0; i < ShopData.getMachineNum(); i++)
			intervalList.add(new LinkedList<TimeInterval>());

		for (i = N / 2; i < N; i++) {
			int opId = permutation[i]; // operation innerIndex
			int jobId = ShopData.getOpById(opId).jobId; // job index

			int selectedMachineId = ShopData.getMachineIdByChoice(opId, permutation[opId - 1]); // machine
																								// assignment

			int processTime = ShopData.getProcessTimeById(opId, selectedMachineId); // processing
																					// time
			boolean flag = false;
			for (j = 0; j < intervalList.get(selectedMachineId - 1).size(); j++) {
				int startPoint = intervalList.get(selectedMachineId - 1).get(j).getStartPoint();
				int endPoint = intervalList.get(selectedMachineId - 1).get(j).getEndPoint();

				max = Math.max(startPoint, curEndTimeOfJob[jobId - 1]);
				if (max + processTime <= endPoint) {
					startTimeInfo.add(new PairData(opId, max));
					curEndTimeOfJob[jobId - 1] = max + processTime;

					if (max > startPoint && endPoint > max + processTime) {
						intervalList.get(selectedMachineId - 1).get(j).setEndPoint(max);
						intervalList.get(selectedMachineId - 1).add(j + 1,
								new TimeInterval(max + processTime, endPoint));
					} else if (max > startPoint) {
						intervalList.get(selectedMachineId - 1).get(j).setEndPoint(max);
					} else if (max + processTime < endPoint) {
						intervalList.get(selectedMachineId - 1).get(j).setStartPoint(max + processTime);
					} else
						intervalList.get(selectedMachineId - 1).remove(j);
					flag = true;
					break;
				}
			}

			if (flag == false) {
				max = Math.max(curEndTimeOfJob[jobId - 1], curEndTimeOfMachine[selectedMachineId - 1]);
				startTimeInfo.add(new PairData(opId, max));
				curEndTimeOfJob[jobId - 1] = max + processTime;
				if (max > curEndTimeOfMachine[selectedMachineId - 1])
					intervalList.get(selectedMachineId - 1)
							.add(new TimeInterval(curEndTimeOfMachine[selectedMachineId - 1], max));
				curEndTimeOfMachine[selectedMachineId - 1] = max + processTime;
			}
		}
		Collections.sort(startTimeInfo);

		max = 0;
		for (i = 0; i < ShopData.getJobNum(); i++) {
			if (curEndTimeOfJob[i] > max)
				max = curEndTimeOfJob[i];
		}

		for (i = 0; i < startTimeInfo.size(); i++)
			permutation[i + N / 2] = startTimeInfo.get(i).getId();

		return max;
	}

	public int run() {
		int iter, i, j;
		initializeParameters();
		initializePopulation();

		for (iter = 1; iter <= NI; iter++) {
			for (i = 0; i < NP; i++) {
				// GA update
				int count = 0;
				j = ran.nextInt(ND);
				do {
					v1[i][j] = w * v0[i][j] + c1 * ran.nextDouble() * (G2[i][j] - G0[i][j])
							+ c2 * ran.nextDouble() * (gBest[j] - G0[i][j]);
					G1[i][j] = G0[i][j] + v1[i][j];
					if (G1[i][j] > delta)
						G1[i][j] = delta;
					if (G1[i][j] < -delta)
						G1[i][j] = -delta;
					j = ++j % ND;
				} while (++count < ND);
			}

			for (i = 0; i < NP; i++) {
				int[] perm = addjustOrder(G1[i], ND);
				if (ran.nextDouble() < Pl) {
					FJSPSolution curSolution = new FJSPSolution(perm, ND);
					FJSPSolution newSolution = new TestLocalSearch(curSolution, localIterTimes).run();
					reArrange(G1[i], newSolution.getPermutation(), ND);
				}

				int val = getFunctionVal(G1[i], ND);
				if (val < solVal[i]) {
					solVal[i] = val;
					G2[i] = (double[]) G1[i].clone(); // G2 personal best G										
				} else
					G2[i] = (double[]) G0[i].clone(); // G0: current
			}

			bestSolVal = Integer.MAX_VALUE;
			bestSolIndex = -1;

			for (i = 0; i < NP; i++) {
				if (solVal[i] < bestSolVal) {
					bestSolVal = solVal[i];
					bestSolIndex = i;
				}
			}

			if (bestSolVal < hisBestSolVal) {
				hisBestSolVal = bestSolVal;
			}

			gBest = G2[bestSolIndex].clone();

			double[][] VX = v0;
			v0 = v1;
			v1 = VX;

			double[][] GX = G0;
			G0 = G2;
			G2 = GX;
			System.out.println("HAPSO iteration:" + iter + ":" + "gBest: " + hisBestSolVal);
		}
		return bestSolVal;
	}

	void assignValue(double[] to, double[] from) {
		for (int i = 0; i < ND; i++)
			to[i] = from[i];
	}

	void reArrange(double vector[], int[] perm, int N) {
		int i;
		ArrayList<Double> list = new ArrayList<Double>();
		for (i = 0; i < N / 2; i++) {
			vector[i] = inverseLinearMapping(perm[i], 1, ShopData.getOptionalMachineNum(i + 1));
			list.add(vector[i + N / 2]);
		}
		Collections.sort(list);
		for (i = N / 2; i < N; i++)
			vector[perm[i] + N / 2 - 1] = list.get(N - 1 - i);
	}

	int[] addjustOrder(double vector[], int N) {
		int i;
		int[] temp = convertVectorToPermutation(vector, N);
		int[] code = convertPermutationToCode(temp, N);
		int[] perm = convertCodeToPermutation(code, N);
		decodingPermutation(perm, N);
		ArrayList<Double> tList = new ArrayList<Double>();

		for (i = N / 2; i < N; i++)
			tList.add(vector[i]);
		Collections.sort(tList);
		for (i = N / 2; i < N; i++)
			vector[perm[i] + N / 2 - 1] = tList.get(N - 1 - i);
		return perm;
	}

	public static void main(String[] args) throws IOException {
		// TODO Auto-generated method stub
//		String[] a = { "01", "02", "03", "04", "05", "06", "07", "08", "09", "10", "11", "12", "13", "14", "15", "16",
//				"17", "18", "19", "21", "22", "25", "26", "29", "30" };
//		for (int aIndex = 0; aIndex < a.length; aIndex++) {
//			for (int totalInteration = 0; totalInteration < 5; totalInteration++) { // 算法独立跑5次{
//				// String fileName =
//				// "E:\\YuanyuanFJSP\\FJSP\\FJSP\\BRdata\\Mk10.fjs";
//				String fileName = "E:\\YuanyuanFJSP\\FJSP\\FJSP\\VLData\\VL" + a[aIndex] + ".fjs";
//				System.out.println(fileName);
//
//				new ShopData(fileName);
//				classPso classPsoTest = new classPso();
//				long initTime = System.currentTimeMillis();
//				int makeSpan = classPsoTest.run();
//
//				String resultFile = "E:\\YuanyuanFJSP\\FJSP\\FJSPResults\\VLdata\\cPSO\\VL" + a[aIndex] + "\\VL"
//						+ a[aIndex] + "_" + totalInteration + ".fjs";
//				try (BufferedWriter bwr = new BufferedWriter(new FileWriter(new File(resultFile)))) {
//					System.out.println(fileName);
//					bwr.write(fileName);
//					bwr.write("\n");
//					bwr.flush();
//					long estimatedTime = System.currentTimeMillis() - initTime;
//					System.out.println(estimatedTime);
//					System.out.println(makeSpan);
//
//					bwr.write("Algorithm Iteration: ");
//					bwr.write("  ");
//					bwr.write(Long.toString(estimatedTime));
//					bwr.write("  ");
//					bwr.write(Integer.toString(makeSpan));
//					bwr.write("\n");
//					bwr.flush();
//				}
//			}
//		}
		String fileName = "E:\\YuanyuanFJSP\\FJSP\\FJSP\\BRdata\\Mk10.fjs";
		new ShopData(fileName);
		HPSO cpso = new HPSO();
		long initTime = System.currentTimeMillis();
		int makeSpan = cpso.run();
		long estimatedTime = System.currentTimeMillis() - initTime;
		System.out.println(makeSpan);
		System.out.println(estimatedTime);
	}

}
