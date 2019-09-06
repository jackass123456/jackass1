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
import cern.jet.random.Distributions;
import common.CometSolPrint;
import common.FJSPSolution;
import common.Operation;
import common.PairData;
import common.ShopData;
import common.SimpleLocalSearch;
import common.Solution;
import common.TestLocalSearch;
import common.TimeInterval;
import de.CDE;

public class CCPSO {
	int NP;
	int NI;
	int ND;

	int[] NG;
	int NGI;
	int[][] groupIndices; 

	double w;
	double c1;
	double c2;
	double Pl;
	double P2;
	double delta;

	int localIterTimes;
	double[] lowerBound;
	double[] upBound;

	Random ran = new Random();

	double[][] v0;
	double[][] v1;
	double[][] G0;
	double[][] G1;
	double[][] G2;
	ArrayList<double[]> G3;

	double[][] L;

	double[] gBest;

	int[] solVal;
	ArrayList<Integer> bestSolVals;

	int bestSolIndex;
	int bestSolVal;
	int historyBestSolVal;

	boolean updated;

	// 分组变量
	ArrayList<int[]> sPbest; // all personal best within all groups
	int[] sBest; // all swarm best value
	double[][] SwarmBest; // all swarm best individual

	void initializeParameters(int [] NG) {
		this.NG = NG;
		NP = 30; // popSize
		NI = 20; // iteration

		ND = ShopData.getTotalOpNum() * 2; // dimension

		NGI = 10;
		P2 = 0.0;

		c1 = 1.57;
		c2 = 1.57;
		w = 0.5;
		delta = 1;

		solVal = new int[NP]; // makespan

		Pl = 0.7;
		localIterTimes = 80;

		lowerBound = new double[ND];
		upBound = new double[ND];

		G0 = new double[NP][]; // current
		G1 = new double[NP][]; // personal
		G2 = new double[NP][];

		G3 = new ArrayList<double[]>();
		bestSolVals = new ArrayList<Integer>();
		sPbest = new ArrayList<int[]>();

		v0 = new double[NP][];
		v1 = new double[NP][];
		L = new double[NP][];

		gBest = new double[ND];

		updated = false;

		int i;

		for (i = 0; i < NP; i++) {
			G0[i] = new double[ND];
			G1[i] = new double[ND];
			G2[i] = new double[ND];
			v0[i] = new double[ND];
			v1[i] = new double[ND];
			L[i] = new double[ND];
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

		historyBestSolVal = bestSolVal;
		gBest = G0[bestSolIndex].clone();

		// LocalBest update
		for (int index = 0; index < NP; index++) {
			int[] tempIndex = new int[3];
			double[] tmpValue = new double[3];
			if (index == 0) {
				tempIndex[0] = NP - 1;
				tempIndex[1] = index;
				tempIndex[2] = index + 1;
			} else if (index == NP - 1) {
				tempIndex[0] = NP - 2;
				tempIndex[1] = NP - 1;
				tempIndex[2] = 0;
			} else {
				tempIndex[0] = index - 1;
				tempIndex[1] = index;
				tempIndex[2] = index + 1;
			}
			for (int dim = 0; dim < tmpValue.length; dim++) {
				tmpValue[dim] = solVal[tempIndex[dim]];
			}
			int bestIndex = getBestAmong(tmpValue[0], tmpValue[1], tmpValue[2]);
			L[index] = G2[tempIndex[bestIndex]].clone();
		}
	}

	void initializeGrouping() {
		// TODO Auto-generated method stub
		int genSize = ND;
		int groupSizeIndex = ran.nextInt(NG.length);
		int groupSize = NG[groupSizeIndex];

		int[] totalIndex = new int[genSize];
		for (int i = 0; i < totalIndex.length; i++) {
			totalIndex[i] = i;
		}
		// 随机打算下标，达到随机分组
		ArrayList<Integer> tmpList = new ArrayList<Integer>();
		for (int index = 0; index < totalIndex.length; index++) {
			tmpList.add(totalIndex[index]);
		}
		Collections.shuffle(tmpList);
		for (int index = 0; index < totalIndex.length; index++) {
			totalIndex[index] = (int) tmpList.get(index);
		}
		// 分组的个数
		int groupNum = genSize % groupSize == 0 ? genSize / groupSize : genSize / groupSize + 1;
		int[][] groupIndexes = new int[groupNum][];
		for (int i = 0; i < groupIndexes.length; i++) {
			// swarm片段长度为剩余index的数量和分组大小中选择最小的那个
			int indexesLength = genSize - i * groupSize;
			indexesLength = indexesLength > groupSize ? groupSize : indexesLength;

			groupIndexes[i] = new int[indexesLength];
			System.arraycopy(totalIndex, i * groupSize, groupIndexes[i], 0, groupIndexes[i].length);
		}
		groupIndices = groupIndexes.clone();

		// 中间保存值

		sBest = new int[groupIndices.length];
		for (int i = 0; i < groupIndices.length; i++) {
			sBest[i] = Integer.MAX_VALUE; // all swarm best value
			sPbest.add(solVal.clone()); // all personal best value within groups
			bestSolVals.add(bestSolVal);
			G3.add(gBest.clone());
		}
	}

	int getBestAmong(double value1, double value2, double value3) {
		if (value1 <= value2 && value1 <= value3) {
			return 0;
		}
		if (value2 <= value1 && value2 <= value3) {
			return 1;
		}
		if (value3 <= value1 && value3 <= value2) {
			return 2;
		}
		return 0;
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

	public int run(int [] groupSize) {
		int iter, i, j;
		initializeParameters(groupSize);
		initializePopulation();
		cern.jet.random.engine.RandomEngine generator;
		generator = new cern.jet.random.engine.MersenneTwister(new java.util.Date());

		for (iter = 1; iter <= NI; iter++) { // iteration of ccpso
			if (iter == 1) {
				initializeGrouping();
			} else {
				if (!updated) {
					initializeGrouping();
				}
			}

			for (int gpIndex = 0; gpIndex < groupIndices.length; gpIndex++) { // iteration
				for (int gpIter = 0; gpIter < NGI; gpIter++) {
					// population update
					for (i = 0; i < NP; i++) {
						for (j = 0; j < groupIndices[gpIndex].length; j++) {
							int dim = groupIndices[gpIndex][j];
							if (ran.nextDouble() <= 0.0) {
								G1[i][dim] = G2[i][dim]
										+ Distributions.nextCauchy(generator) * Math.abs(G2[i][dim] - L[i][dim]);
							} else {
								G1[i][dim] = L[i][dim] + ran.nextGaussian() * Math.abs(G2[i][dim] - L[i][dim]);
							}
							if (G1[i][dim] > delta)
								G1[i][dim] = delta;
							if (G1[i][dim] < -delta)
								G1[i][dim] = -delta;
						}
					} // end for population

					// evolution operators
					for (i = 0; i < NP; i++) {
						double[] newG1 = replace(ND, gpIndex, gBest, G1[i]);
						int[] perm = addjustOrder(newG1, ND);
						if (ran.nextDouble() < Pl) {
							FJSPSolution curSolution = new FJSPSolution(perm, ND);
							FJSPSolution newSolution = new TestLocalSearch(curSolution, localIterTimes).run();
							reArrange(newG1, newSolution.getPermutation(), ND);
						}
						int val = getFunctionVal(newG1, ND);
						if (val < sPbest.get(gpIndex)[i]) {
							sPbest.get(gpIndex)[i] = val;
							for (int dim = 0; dim < groupIndices[gpIndex].length; dim++) {
								int curDim = groupIndices[gpIndex][dim];
								G2[i][curDim] = newG1[curDim];
							}
							if (val < bestSolVals.get(gpIndex)) { // 记录分组内最优值及最优个体
								bestSolVals.set(gpIndex, val);
								G3.set(gpIndex, newG1);
							}
						}
					} // end for population

					// LocalBest update
					for (int index = 0; index < NP; index++) {
						int[] tempIndex = new int[3];
						double[] tmpValue = new double[3];
						if (index == 0) {
							tempIndex[0] = NP - 1;
							tempIndex[1] = index;
							tempIndex[2] = index + 1;
						} else if (index == NP - 1) {
							tempIndex[0] = NP - 2;
							tempIndex[1] = NP - 1;
							tempIndex[2] = 0;
						} else {
							tempIndex[0] = index - 1;
							tempIndex[1] = index;
							tempIndex[2] = index + 1;
						}
						for (int dim = 0; dim < tmpValue.length; dim++) {
							tmpValue[dim] = solVal[tempIndex[dim]];
						}
						int bestIndex = getBestAmong(tmpValue[0], tmpValue[1], tmpValue[2]);
						for(int dimIndex = 0; dimIndex < groupIndices[gpIndex].length; dimIndex++){
							int dim = groupIndices[gpIndex][dimIndex];
							L[index][dim] = G2[tempIndex[bestIndex]][dim];
						}
						//L[index] = G2[tempIndex[bestIndex]].clone();
					} // end for population
				} // end for inner iteration
			} // end for group size

			int totalBestSolVal = Integer.MAX_VALUE;
			int totalBestSolIndex = -1;

			for (int gpIndex = 0; gpIndex < bestSolVals.size(); gpIndex++) {
				if (bestSolVals.get(gpIndex) < totalBestSolVal) {
					totalBestSolVal = bestSolVals.get(gpIndex);
					totalBestSolIndex = gpIndex;
				}
			}
			
			if (totalBestSolVal < historyBestSolVal) {
				historyBestSolVal = totalBestSolVal;
				gBest = G3.get(totalBestSolIndex).clone();
				updated = true;
			}
			System.out.println( "The " + iter + "th iteration: " + ", swarmBestSolVal: " + historyBestSolVal);
		}
		return historyBestSolVal;
		
	}

	double[] replace(int D, int gpIndex, double[] ref, double[] tar) {
		double[] newG1 = ref.clone();
		for (int dim = 0; dim < groupIndices[gpIndex].length; dim++) {
			int curDim = groupIndices[gpIndex][dim];
			newG1[curDim] = tar[curDim];
		}
		return newG1;
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
//		int[][] groupSizes = { { 50, 100, 200 }, { 50, 100, 200, 300 }, { 100, 200, 300 }, { 100, 200, 300, 400 } };
//		for (int fileIndex = 0; fileIndex < a.length; fileIndex++) {
//			int[] groupSizeSpec = null;
//			if (fileIndex <= 3 && fileIndex >= 0) {
//				groupSizeSpec = groupSizes[0];
//			}
//			if (fileIndex <= 13 && fileIndex >= 4) {
//				groupSizeSpec = groupSizes[1];
//			}
//			if (fileIndex <= 20 && fileIndex >= 14) {
//				groupSizeSpec = groupSizes[2];
//			}
//			if (fileIndex <= 24 && fileIndex >= 21) {
//				groupSizeSpec = groupSizes[3];
//			}
//			String fileName = "E:\\YuanyuanFJSP\\FJSP\\FJSP\\VLData\\VL" + a[fileIndex] + ".fjs";
//			for (int totalInteration = 0; totalInteration < 5; totalInteration++) { // 算法独立跑5次
//				String resultFile = "E:\\YuanyuanFJSP\\FJSP\\FJSPResults\\VLdata\\hdEA\\VLData\\VL" + a[fileIndex]
//						+ "\\VL" + a[fileIndex] +"_"+ totalInteration+ ".fjs";
//				try (BufferedWriter bwr = new BufferedWriter(new FileWriter(new File(resultFile)))) {
//					System.out.println(fileName);
//					bwr.write(fileName);
//					bwr.write("\n");
//					bwr.flush();
//					
//					new ShopData(fileName);
//					dhEA dhEATest = new dhEA();
//					long initTime = System.currentTimeMillis();
//					int makeSpan = dhEATest.run(groupSizeSpec);
//					long estimatedTime = System.currentTimeMillis() - initTime;
//					System.out.println(estimatedTime);
//					bwr.write(Long.toString(estimatedTime));
//					bwr.write("\n");
//					bwr.flush();
//					
//					System.out.println(makeSpan);
//					bwr.write(Long.toString(makeSpan));
//					bwr.write("\n");
//					bwr.flush();
//				}
//			}
//		}
		int [] groupSizeSpec = {120,240,480};
		String fileName = "E:\\YuanyuanFJSP\\FJSP\\FJSP\\BRdata\\Mk10.fjs";
		new ShopData(fileName);
		CCPSO dhEATest = new CCPSO();
		long initTime = System.currentTimeMillis();
		int makeSpan = dhEATest.run(groupSizeSpec);
		long estimatedTime = System.currentTimeMillis() - initTime;
		System.out.println(makeSpan);
		System.out.println(estimatedTime);
	}
}
