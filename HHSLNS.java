package TFSCompared;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.Random;
import java.util.Scanner;
import java.util.Timer;

import MRLS.RandomStartLocalSearch;

import common.CometSolPrint;
import common.FJSPSolution;
import common.Operation;
import common.PairData;
import common.ShopData;
import common.SimpleLocalSearch;
import common.Solution;
import common.TestLocalSearch;
import common.TimeInterval;

public class HHSLNS {
	int NP;
	int NI;
	int ND;

	double F;
	double Cr;
	double Pl;
	int delta;

	int localIterTimes;

	double[] lowerBound;
	double[] upBound;

	Random ran = new Random();

	double[][] G0;
	double[][] G1;
	double[][] G2;

	int[] solVal;

	int bestSolIndex;
	int bestSolVal;

	void initializeParameters() {
		NP = 30; // popSize
		NI = 200; // iteration

		ND = ShopData.getTotalOpNum() * 2; // dimension

		F = 0.05;
		Cr = 0.1;

		delta = 1;

		solVal = new int[NP]; // makespan

		Pl = 0.7;
		localIterTimes = 80;

		lowerBound = new double[ND];
		upBound = new double[ND];

		G0 = new double[NP][]; // current
		G1 = new double[NP][]; // personal
		G2 = new double[NP][];

		int i;

		for (i = 0; i < NP; i++) {
			G0[i] = new double[ND];
			G1[i] = new double[ND];
			G2[i] = new double[ND];
		}

		for (i = 0; i < ND; i++) {
			lowerBound[i] = -delta;
			upBound[i] = delta;
		}
	}

	void initializePopulation() {
		int i, j;
		for (i = 0; i < NP; i++) {
			for (j = 0; j < ND; j++)
				G0[i][j] = lowerBound[j] + (upBound[j] - lowerBound[j]) * ran.nextDouble();
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
	}

	public int run() {
		// count = 0;
		// Timer timer = new Timer();
		// timer.schedule(new MyTask(), 40, 5000);

		int iter, i, j;
		initializeParameters();
		initializePopulation();

		for (iter = 1; iter <= NI; iter++) {
			for (i = 0; i < NP; i++) {
				// DE update
				int R1, R2;
				do {
					R1 = ran.nextInt(NP);
				} while (R1 == i);

				do {
					R2 = ran.nextInt(NP);
				} while (R2 == i || R2 == R1);
				int count = 0;
				j = ran.nextInt(ND);
				do {
					if (ran.nextDouble() < Cr) {
						G1[i][j] = G0[bestSolIndex][j] + F * (G0[R1][j] - G0[R2][j]);
						if (G1[i][j] > delta)
							G1[i][j] = delta;
						if (G1[i][j] < -delta)
							G1[i][j] = -delta;
					} else
						G1[i][j] = G0[i][j];

					j = ++j % ND;
				} while (++count < ND);
			}

			for (i = 0; i < NP; i++) {
				int[] perm = addjustOrder(G1[i], ND);
				if (ran.nextDouble() < 0.3) {

					// Solution curSolution = new Solution(perm, ND);

					// Solution newSolution = new SimpleLocalSearch(curSolution,
					// localIterTimes).run();

					// reArrange(G1[i], newSolution.getPermutation(), ND);

					FJSPSolution curSolution = new FJSPSolution(perm, ND);
					// System.out.println("Old: " + curSolution.getMakeSpan());

					FJSPSolution newSolution = new TestLocalSearch(curSolution, localIterTimes).run();
					// if (newSolution.getMakeSpan() == 307){
					// System.out.println(newSolution.getMakeSpan() + " " +
					// newSolution.getWorkLoad()[1] + " " +
					// newSolution.getWorkLoad()[0]);
					// }
					// System.out.println("New: " + newSolution.getMakeSpan());
					reArrange(G1[i], newSolution.getPermutation(), ND);
					// System.out.println("old: " + newSolution.getMakeSpan());
				}
				int val = getFunctionVal(G1[i], ND);
				// System.out.println("new: " + val);
				if (val < solVal[i]) {
					solVal[i] = val;
					G2[i] = (double[]) G1[i].clone(); // G2 personal best G1:
														// cur after local
														// search
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
			double[][] GX = G0;
			G0 = G2;
			G2 = GX;
			System.out.println("Iteration:" + iter + ":" + "gBest: " + bestSolVal);
		} /*
			 * System.out.println("old: " + bestSolVal); bestSolVal =
			 * Integer.MAX_VALUE; bestSolIndex = -1; for (i = 0; i < NP; i++) {
			 * int[] perm = addjustOrder(G0[i], ND);
			 * 
			 * Solution curSolution = new Solution(perm, ND);
			 * 
			 * Solution newSolution = new SimpleLocalSearch(curSolution,
			 * localIterTimes).runAllAnother(); if (newSolution.getMakeSpan() <
			 * bestSolVal) bestSolVal = newSolution.getMakeSpan(); }
			 */
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

	int[] convertVectorToPermutation(double vector[], int N) {
		ArrayList<PairData> tList = new ArrayList<PairData>();
		int i;
		for (i = N / 2; i < N; i++)
			tList.add(new PairData(i - N / 2 + 1, vector[i]));
		Collections.sort(tList);
		/*
		 * for (i = N / 2 - 1; i >= 1; i--) {
		 * 
		 * if (tList.get(i).getVal() == tList.get(i - 1).getVal()) { if (i != N
		 * / 2 - 1) { tList.get(i).addVal( (tList.get(i + 1).getVal() -
		 * tList.get(i).getVal()) / (N / 2)); } else
		 * tList.get(i).addVal(0.0000000001); } }
		 */
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

	public static String[] getNames(String filePath, int runId) {
		String fileName = filePath.substring(filePath.lastIndexOf("\\") + 1);

		String[] str = fileName.split("\\.");
		// String root = "H:\\yuanyuan\\NTestHHSLNS\\v\\" + str[0] +
		// "_ExperimentalResult";
		String root = "F:\\HHSLNS_DPResults\\" + str[0] + "_ExperimentalResult";
		File file = new File(root);
		if (!file.exists())
			file.mkdir();
		String[] names = new String[5];
		names[0] = root + "\\" + str[0] + "_r" + "_" + runId + ".fjs";
		names[1] = root + "\\" + str[0] + "_start" + "_" + runId + ".txt";
		names[2] = root + "\\" + str[0] + "_out" + "_" + runId + ".txt";
		names[3] = root + "\\" + str[0] + "_runInfo" + "_" + runId + ".txt";
		names[4] = root + "\\" + str[0] + "_sol" + "_" + runId + ".txt";
		return names;
	}

	/*
	 * public static void integratedSearch(String filePath, int runId){ new
	 * ShopData(filePath); String[] names = getNames(filePath, runId); String
	 * rName = names[0]; String sName = names[1]; String oName = names[2];
	 * String infoName = names[3]; String solName = names[4];
	 * 
	 * CDE cde = new CDE(); long startTime = System.currentTimeMillis(); int
	 * makespan = cde.run(); long endTime = System.currentTimeMillis();
	 * 
	 * int[][] perm; int i, j; perm = new int[hs.HMS][]; for (i = 0; i < hs.HMS;
	 * i++) perm[i] = new int[hs.N];
	 * 
	 * for (i = 0; i < hs.HMS; i++){ int val =
	 * hs.getFunctionVal(hs.harmonyMemory[i], hs.N); perm[i] =
	 * hs.convertVectorToPermutation(hs.harmonyMemory[i], hs.N);
	 * System.out.println(val); print(perm[i]); } int k = 0; int t = 0;
	 * 
	 * ArrayList<ArrayList<Integer>> table = new
	 * ArrayList<ArrayList<Integer>>(); for (j = 0; j <
	 * ShopData.getTotalOpNum(); j++){ ArrayList<Integer> list = new
	 * ArrayList<Integer>(); list.add(perm[hs.bestSolIndex][j]);
	 * table.add(list); } int[] choice = new int[ShopData.getMachineNum() + 1];
	 * for (j = 0; j < ShopData.getTotalOpNum(); j++) { if
	 * (ShopData.getOptionalMachineNum(j + 1) > 1) { for (i = 1; i <=
	 * ShopData.getMachineNum(); i++) choice[i] = 0; for (i = 0; i < hs.HMS;
	 * i++){ if (perm[i][j] != table.get(j).get(0)) choice[perm[i][j]]++; } int
	 * index = 1; int max = 0; for (i = 1; i <= ShopData.getMachineNum(); i++){
	 * if (choice[i] > max){ max = choice[i]; index = i; } } if (max >= 2)
	 * table.get(j).add(index); } }
	 * 
	 * 
	 * for (j = 0; j < ShopData.getTotalOpNum(); j++){ if (table.get(j).size()
	 * == 1) k++; else if (table.get(j).size() == 2) t++; }
	 * 
	 * int u = 0; for (i = 0; i < ShopData.getTotalOpNum(); i++){ if
	 * (ShopData.getOptionalMachineNum(i + 1) > 1){ for (j = 0; j < hs.HMS - 1;
	 * j++){ if (perm[j][i] != perm[j + 1][i]) break; } if (j == hs.HMS - 1)
	 * u++; } }
	 * 
	 * try { OutputStreamWriter swr = new OutputStreamWriter( new
	 * FileOutputStream(infoName)); PrintWriter pwr = new PrintWriter(swr);
	 * pwr.println("One Choice: " + k); pwr.println("Two Choice: " + t);
	 * pwr.println("ͨ��ѧϰ,����ѡ���ж��ֱ�ɶ���ͬ�Ĳ�����:  " + u); pwr.println(
	 * "Flex: " + (double)(k + t * 2) / (k + t)); pwr.println("��������ʱ�䣺 " +
	 * (endTime - startTime) + "ms"); pwr.println("�Ż�ֵ: " + makespan);
	 * 
	 * pwr.close();
	 * 
	 * } catch (IOException e) { // TODO Auto-generated catch block
	 * e.printStackTrace(); } Solution sol = new Solution(hs.getBestPerm(),
	 * ShopData.getTotalOpNum() * 2); sol.printToText(sName);
	 * 
	 * int n = 0; try { OutputStreamWriter osw = new OutputStreamWriter(new
	 * FileOutputStream(rName)); PrintWriter pw = new PrintWriter(osw);
	 * pw.print(ShopData.getJobNum() + " "); pw.print(ShopData.getMachineNum() +
	 * " "); pw.println(ShopData.getTotalOpNum());
	 * 
	 * for (int job = 1; job <= ShopData.getJobNum(); job++){
	 * pw.print(ShopData.getOpNumInJob(job) + " "); for (u = 1; u
	 * <=ShopData.getOpNumInJob(job); u++ ){ n++; int choiceNum = table.get(n -
	 * 1).size(); pw.print(choiceNum + " "); for (int v = 1; v <= choiceNum;
	 * v++){ int mId = ShopData.getMachineIdByChoice(n, table.get(n - 1).get(v -
	 * 1)); int processTime = ShopData.getProcessTimeByChoice(n, table.get(n -
	 * 1).get(v - 1)); pw.print(mId + " " + processTime + " "); }
	 * 
	 * } pw.println();
	 * 
	 * } pw.close(); } catch (IOException e) { // TODO Auto-generated catch
	 * block e.printStackTrace(); } System.out.println("hello world"); LNS lns =
	 * new LNS(rName, sName, oName); lns.run(); try {
	 * CometSolPrint.cometSolPrint(filePath, oName, solName); } catch
	 * (IOException e) { // TODO Auto-generated catch block e.printStackTrace();
	 * } }
	 */
	public static void main(String[] args) throws IOException {
//		String[] a = { "01", "02", "03", "04", "05", "06", "07", "08", "09", "10", "11", "12", "13", "14", "15", "16",
//				"17", "18", "19", "21", "22", "25", "26", "29", "30" };
//		for (int aIndex = 0; aIndex < a.length; aIndex++) {
//			for (int totalInteration = 0; totalInteration < 5; totalInteration++) { // 算法独立跑5次{
//				String fileName = "E:\\YuanyuanFJSP\\FJSP\\FJSP\\VLData\\VL" + a[aIndex] + ".fjs";
//				System.out.println(fileName);
//
//				new ShopData(fileName);
//				CDE cde = new CDE();
//				long initTime = System.currentTimeMillis();
//				int makeSpan = cde.run();
//
//				String resultFile = "E:\\YuanyuanFJSP\\FJSP\\FJSPResults\\VLdata\\cDE\\VL" + a[aIndex] + "\\VL"
//						+ a[aIndex] + "_" + totalInteration + ".fjs";
//				
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
		
		for(int totalInteration = 0; totalInteration < 5; totalInteration++){
			String fileName = "E:\\YuanyuanFJSP\\FJSP\\FJSP\\BRData\\Mk10.fjs";
			new ShopData(fileName);
			HHSLNS cde = new HHSLNS();
			long initTime = System.currentTimeMillis();
			int makeSpan = cde.run();
			long estimatedTime = System.currentTimeMillis() - initTime;
			System.out.println(estimatedTime);
			System.out.println(makeSpan);
		}
	}

	static void analysisResult(int[] mArray, long[] cpuTime, int runTimes) {
		int min = Integer.MAX_VALUE;
		int sumMakespan = 0;
		long sumCPU = 0;

		for (int i = 0; i < runTimes; i++) {
			if (mArray[i] < min)
				min = mArray[i];
			sumMakespan += mArray[i];
			sumCPU += cpuTime[i];
		}
		double average = (double) (sumMakespan) / runTimes;
		double cpu = (double) (sumCPU) / runTimes;

		double sd = 0;

		for (int i = 0; i < runTimes; i++) {
			sd += (mArray[i] - average) * (mArray[i] - average);
		}
		sd = Math.pow(sd / (runTimes - 1), 0.5);

		System.out.println();
		System.out.println("Best: " + min);
		System.out.println("Average: " + average);
		System.out.println("SD: " + sd);
		System.out.println("CPU: " + cpu + "ms");

	}

	static double[] analysisResult_N(int[] mArray, long[] cpuTime, int runTimes) {

		double[] result = new double[4];

		int min = Integer.MAX_VALUE;
		int sumMakespan = 0;
		long sumCPU = 0;

		for (int i = 0; i < runTimes; i++) {
			if (mArray[i] < min)
				min = mArray[i];
			sumMakespan += mArray[i];
			sumCPU += cpuTime[i];
		}
		double average = (double) (sumMakespan) / runTimes;
		double cpu = (double) (sumCPU) / runTimes;

		double sd = 0;

		for (int i = 0; i < runTimes; i++) {
			sd += (mArray[i] - average) * (mArray[i] - average);
		}
		sd = Math.pow(sd / (runTimes - 1), 0.5);

		result[0] = min;
		result[1] = average;
		result[2] = sd;
		result[3] = cpu;
		return result;

	}

	int count = 0;

	class MyTask extends java.util.TimerTask {
		@Override
		public void run() {
			// TODO Auto-generated method stub
			System.out.println(count * 5 + " " + bestSolVal);
			count++;
		}
	}
}
