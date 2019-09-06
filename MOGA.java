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
import java.util.Arrays;
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

public class MOGA {
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

		F = 0.1;
		Cr = 0.3;

		delta = 1;

		solVal = new int[NP]; // makespan

		if(ShopData.getTotalOpNum()==240){
			Pl = 0.2;
		}
		else{
			Pl = 0.05;
		}
		
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

	void initializePopulation() throws Exception {
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
	
	int getOpIndex(int opId, int[] jobNums) {
		int opIndex = -1;
		for (int i = -1; i < jobNums.length - 1; i++) {
			if (i == -1) {
				if (opId >= 0 && opId <= jobNums[i + 1]) {
					opIndex = opId - 0;
					break;
				} else
					continue;
			}
			if (opId >= jobNums[i] && opId <= jobNums[i + 1]) {
				opIndex = opId - jobNums[i];
				break;
			}
		}
		if (opIndex == -1) {
			opIndex = opId - 0;
		}

		if (opIndex == -1) {
			System.out.println("ERROR");
		}
		if (opIndex == 0) {
			System.out.println("ERROR");
		}
		return opIndex;
	}
	int[] getSequence(double vector[], int N) {
		int[] sequence = new int[ShopData.getTotalOpNum() * 3];
		int[] temp = convertVectorToPermutation(vector, N);
		int[] code = convertPermutationToCode(temp, N);
		int[] perm = convertCodeToPermutation(code, N);
		// int [] perm = {1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 3, 1,
		// 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 1,
		// 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 1,
		// 44, 22, 39, 1, 50, 7, 51, 34, 2, 28, 12, 23, 8, 45, 46, 40, 9, 29,
		// 52, 47, 10, 48, 3, 53, 24, 35, 4, 5, 17, 25, 54, 18, 11, 13, 41, 55,
		// 36, 30, 19, 49, 26, 20, 6, 14, 15, 42, 37, 31, 32, 21, 43, 27, 16,
		// 38,33};
        //int [] perm = {4, 10, 4, 10, 3, 2, 3, 9, 3, 7, 7, 3, 8, 2, 1, 5, 1, 6, 9, 6, 7, 4, 8, 8, 9, 8, 2, 1, 7, 3, 6, 8, 10, 8, 5, 7, 1, 9, 1, 4, 
        //25, 33, 37, 21, 1, 26, 13, 9, 10, 5, 29, 17, 38, 2, 14, 6, 22, 3, 18, 30, 19, 39, 34, 31, 4, 11, 27, 7, 23, 35, 15, 32, 20, 40, 36, 16, 28, 12, 8, 24};
		int[] jobNums = new int[ShopData.getJobNum()];
		int sumOpNums = 0;
		for (int i = 0; i < jobNums.length; i++) {
			jobNums[i] = sumOpNums + ShopData.getOpNumInJob(i + 1);
			sumOpNums = sumOpNums + ShopData.getOpNumInJob(i + 1);
		}

		int i;

		for (i = N / 2; i < N; i++) {
			int opId = perm[i]; // operation innerIndex
			int jobId = ShopData.getOpById(opId).jobId; // job index
			int selectedMachineId = ShopData.getMachineIdByChoice(opId, perm[opId - 1]); // machine
																							// assignment

			int opIndex = getOpIndex(opId, jobNums);
			int index = i - N / 2;
			sequence[index * 3 + 0] = jobId - 1;
			sequence[index * 3 + 1] = opIndex - 1;
			sequence[index * 3 + 2] = selectedMachineId;

			if (sequence[index * 3 + 0] == -1 || sequence[index * 3 + 1] == -1 || sequence[index * 3 + 2] == -1) {
				System.out.println("ERROR");
			}
		}

		// System.out.println(Arrays.toString(sequence2));
		// System.out.println(Arrays.toString(sequence));

		return sequence;
	}

	public int run() throws Exception {
		int iter, i, j;
		initializeParameters();
		initializePopulation();

		for (iter = 1; iter <= NI; iter++) {
			
			for (i = 0; i < NP; i++) {
				// genetic update
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
				if (ran.nextDouble() < 0.5) {
					FJSPSolution curSolution = new FJSPSolution(perm, ND);
					FJSPSolution newSolution = new TestLocalSearch(curSolution, localIterTimes).run();
					reArrange(G1[i], newSolution.getPermutation(), ND);
				}
				int val = getFunctionVal(G1[i], ND);
				if (val < solVal[i]) {
					solVal[i] = val;
					G2[i] = (double[]) G1[i].clone(); 
				} else
					G2[i] = (double[]) G0[i].clone(); 
			}

			bestSolVal = Integer.MAX_VALUE;
			bestSolIndex = -1;

			for (i = 0; i < NP; i++) {
				if (solVal[i] < bestSolVal) {
					bestSolVal = solVal[i];
					bestSolIndex = i;
				}
			}
			
			System.out.println("MOGA iteration:" + iter + ":" + "gBest: " + bestSolVal);
			double[][] GX = G0;
			G0 = G2;
			G2 = GX;
			
			
//			if (iter == NI) {
//				int[] sequence = getSequence(G2[bestSolIndex], ND);
//				System.out.println(bestSolVal);
//				System.out.println(Arrays.toString(sequence));
//
//				StringBuilder instance = new StringBuilder();

				// instance.append("Mkp: ");
				// instance.append(bestSolVal);
				// instance.append(":");
//				for (int ii = 0; ii < sequence.length; ii++) {
//					instance.append(sequence[ii]);
//					instance.append(" ");
//				}
//
//				instance.append("\n");
//				try (BufferedWriter bwr = new BufferedWriter(new FileWriter(new File(solutionPath)))) {
//					bwr.write(instance.toString());
//					bwr.flush();
//				} catch (IOException e) {
//					e.printStackTrace();
//				}
			//}
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

	int getFunctionVal(double vector[], int N) throws Exception {
		int i;
		int[] temp = convertVectorToPermutation(vector, N);
		int[] code = convertPermutationToCode(temp, N);
		int[] perm = convertCodeToPermutation(code, N);
		int val = decodingPermutation(perm, N);
		ArrayList<Double> tList = new ArrayList<Double>();
		//Thread.sleep(1000);
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
		// String root = "H:\\yuanyuan\\NTestHHSLNS\\v\\" + str[0] + "_ExperimentalResult";
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
	
	public static void main(String[] args) throws Exception {
		
		for(int totalInteration = 0; totalInteration < 5; totalInteration++){
			String fileName = "E:\\YuanyuanFJSP\\FJSP\\FJSP\\BRData\\Mk10.fjs";
			new ShopData(fileName);
			MOGA moga = new MOGA();
			long initTime = System.currentTimeMillis();
			int makeSpan = moga.run();
			long estimatedTime = System.currentTimeMillis() - initTime;
			System.out.println(estimatedTime);
			System.out.println(makeSpan);
		}
//		String sIndices[] = { "L", "M", "R" };
//		for (int caseIndex = 0; caseIndex < 5; caseIndex++) {
//			for (int sIndex = 0; sIndex < sIndices.length; sIndex++) {
//				String dataPath = "E:\\YuanyuanFJSP\\fFJSP\\Lei\\case" + (caseIndex + 1) + sIndices[sIndex] + ".fjs";
//				System.out.println("dataPath:" + dataPath);
//
//				for (int i = 1; i <= 10; i++) {
//					new ShopData(dataPath);
//
//					MOGA classPsoTest = new MOGA();
//					long initTime = System.currentTimeMillis();
//
//					String solutionPath = "E:\\YuanyuanFJSP\\fFJSP\\LeiSolutions\\MOGA\\case" + (caseIndex + 1) + "\\" + "case" + (caseIndex + 1) + sIndices[sIndex] + "_" + i + ".txt";
//					System.out.println("solutionPath:" + solutionPath);
//
//					int makeSpan = classPsoTest.run(solutionPath);
//					long estimatedTime = System.currentTimeMillis() - initTime;
//					System.out.println(estimatedTime);
//					System.out.println(makeSpan);
//				}
//			}
//		}
//	}

	}
}

