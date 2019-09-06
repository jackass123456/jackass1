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

import common.FJSPSolution;
import common.Operation;
import common.PairData;
import common.ShopData;

import common.TestLocalSearch;
import common.TimeInterval;

import cern.jet.random.Distributions;

public class MAPSO {
	int NP;
	int NI;
	int ND;

	int[] NG = {240,480};
	int[][] groupIndices;

	double w;
	double c1;
	double c2;
	double Pl;
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

	public double[] gBest;

	int[] solVal;
	int bestSolIndex;

	int bestSolVal;
	int historyBestSolVal;

	boolean updated;

	ArrayList<int[]> sPbest; // all personal best within all groups
	int[] sBest; // all swarm best value
	double[][] SwarmBest; // all swarm best individual
	ArrayList<Integer> bestSolVals;

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
		G1 = new double[NP][]; // personal
		G2 = new double[NP][];
		G3 = new ArrayList<double[]>();

		SwarmBest = new double[NP][];

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
			SwarmBest[i] = new double[ND];
		}

		for (i = 0; i < ND; i++) {
			lowerBound[i] = -delta;
			upBound[i] = delta;
		}

		sPbest = new ArrayList<int[]>(); // all personal best values within all
											// groups
		bestSolVals = new ArrayList<Integer>(); // all swarm best valus
	}

	void initializePopulation() throws Exception {
		int i, j;
		for (i = 0; i < NP; i++) {
			for (j = 0; j < ND; j++) {
				G0[i][j] = lowerBound[j] + (upBound[j] - lowerBound[j]) * ran.nextDouble();
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
		// 闅忔満鎵撶畻涓嬫爣锛岃揪鍒伴殢鏈哄垎缁�
		ArrayList<Integer> tmpList = new ArrayList<Integer>();
		for (int index = 0; index < totalIndex.length; index++) {
			tmpList.add(totalIndex[index]);
		}
		Collections.shuffle(tmpList);
		for (int index = 0; index < totalIndex.length; index++) {
			totalIndex[index] = (int) tmpList.get(index);
		}
		// 鍒嗙粍鐨勪釜鏁�
		int groupNum = genSize % groupSize == 0 ? genSize / groupSize : genSize / groupSize + 1;
		int[][] groupIndexes = new int[groupNum][];
		for (int i = 0; i < groupIndexes.length; i++) {
			// swarm鐗囨闀垮害涓哄墿浣檌ndex鐨勬暟閲忓拰鍒嗙粍澶у皬涓�夋嫨鏈�灏忕殑閭ｄ釜
			int indexesLength = genSize - i * groupSize;
			indexesLength = indexesLength > groupSize ? groupSize : indexesLength;

			groupIndexes[i] = new int[indexesLength];
			System.arraycopy(totalIndex, i * groupSize, groupIndexes[i], 0, groupIndexes[i].length);
		}
		groupIndices = groupIndexes.clone();

		// 涓棿淇濆瓨鍊�
		sBest = new int[groupIndices.length];
		for (int i = 0; i < groupIndices.length; i++) {
			sBest[i] = Integer.MAX_VALUE; // all swarm best value
			sPbest.add(solVal.clone()); // all personal best value within groups
			G3.add(gBest.clone()); // all swarm best individual
			bestSolVals.add(bestSolVal);
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
        //int [] perm = {
        //4, 10, 4, 10, 3, 2, 3, 9, 3, 7, 7, 3, 8, 2, 1, 5, 1, 6, 9, 6, 7, 4, 8, 8, 9, 8, 2, 1, 7, 3, 6, 8, 10, 8, 5, 7, 1, 9, 1, 4, 
        //25, 33, 37, 21, 1, 26, 13, 9, 10, 5, 29, 17, 38, 2, 14, 6, 22, 3, 18, 30, 19, 39, 34, 31, 4, 11, 27, 7, 23, 35, 15, 32, 20, 40, 36, 16, 28, 12, 8, 24};
		int[] jobNums = new int[ShopData.getJobNum()];
		int sumOpNums = 0;
		for (int i = 0; i < jobNums.length; i++) {
			jobNums[i] = sumOpNums + ShopData.getOpNumInJob(i + 1);
			sumOpNums = sumOpNums + ShopData.getOpNumInJob(i + 1);
		}

		ArrayList<LinkedList<TimeInterval>> intervalList = new ArrayList<LinkedList<TimeInterval>>(
				ShopData.getMachineNum());
		int i;
		// for (i = 0; i < ShopData.getMachineNum(); i++)
		// intervalList.add(new LinkedList<TimeInterval>());

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

	double[] replace(int D, int gpIndex, double[] ref, double[] tar) {
		double[] newG1 = ref.clone();
		for (int dim = 0; dim < groupIndices[gpIndex].length; dim++) {
			int curDim = groupIndices[gpIndex][dim];
			newG1[curDim] = tar[curDim];
		}
		return newG1;
	}

	public int run(String solutionPath) throws Exception {
		int iter, i, j;
		initializeParameters();
		initializePopulation();
		cern.jet.random.engine.RandomEngine generator;
		generator = new cern.jet.random.engine.MersenneTwister(new java.util.Date());

		for (iter = 1; iter <= NI; iter++) { // iteration of gapso
			if (iter == 1) {
				initializeGrouping();
			} 
			for (int gpIndex = 0; gpIndex < groupIndices.length; gpIndex++) { // iteration
				// PSO position update
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
				}

				// cooperative evolution
				for (i = 0; i < NP; i++) {
					double[] newG1 = replace(ND, gpIndex, gBest, G1[i]);
					int[] perm = addjustOrder(newG1, ND);
					if (ran.nextDouble() < 0.7) {
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
						if (val < bestSolVals.get(gpIndex)) {
							bestSolVals.set(gpIndex, val);
							G3.set(gpIndex, newG1.clone());
						}
					}
				}

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

				double[] newG3 = replace(ND, gpIndex, gBest, G3.get(gpIndex));
				int[] perm2 = addjustOrder(newG3, ND);
				if (ran.nextDouble() < Pl) {
					FJSPSolution curSolution = new FJSPSolution(perm2, ND);
					FJSPSolution newSolution = new TestLocalSearch(curSolution, localIterTimes).run();
					reArrange(newG3, newSolution.getPermutation(), ND);
				}
				int val2 = getFunctionVal(newG3, ND);
				if (val2 < bestSolVal) {
					bestSolVal = val2;
					for (int dim = 0; dim < groupIndices[gpIndex].length; dim++) {
						int curDim = groupIndices[gpIndex][dim];
						gBest[curDim] = G3.get(gpIndex)[curDim];
					}
				}

				double[][] VX = v0;
				v0 = v1;
				v1 = VX;

				double[][] GX = G0;
				G0 = G2;
				G2 = GX;
			}

			if (bestSolVal < historyBestSolVal) {
				historyBestSolVal = bestSolVal;
				updated = true;
			}
			System.out.println("MAPSO iteration:" + iter + ":" + "gBest: " + historyBestSolVal);
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

	public static void main(String[] args) throws Exception {
		// TODO Auto-generated method stub
//		String sIndices[] = { "L", "M", "R" };
//		for (int caseIndex = 2; caseIndex < 5; caseIndex++) {
//			for (int sIndex = 0; sIndex < sIndices.length; sIndex++) {
//				String dataPath = "E:\\YuanyuanFJSP\\fFJSP\\Lei\\case" + (caseIndex + 1) + sIndices[sIndex] + ".fjs";
//				System.out.println("dataPath:" + dataPath);
//
//				for (int i = 1; i <= 12; i++) {
//					new ShopData(dataPath);
//
//					MAPSO classPsoTest = new MAPSO();
//					long initTime = System.currentTimeMillis();
//
//					String solutionPath = "E:\\YuanyuanFJSP\\fFJSP\\LeiSolutions\\MAPSO\\case" + (caseIndex + 1) + "\\"
//							+ "case" + (caseIndex + 1) + sIndices[sIndex] + "_" + i + ".txt";
//					System.out.println("solutionPath:" + solutionPath);
//
//					int makeSpan = classPsoTest.run(solutionPath);
//					long estimatedTime = System.currentTimeMillis() - initTime;
//					System.out.println(estimatedTime);
//					System.out.println(makeSpan);
//				}
//			}
//		}

		// single test
		 String dataPath = "E:\\YuanyuanFJSP\\FJSP\\FJSP\\BRdata\\Mk10.fjs";
		 new ShopData(dataPath);
		
		 MAPSO mapso = new MAPSO();
		 long initTime = System.currentTimeMillis();
		
		 String solutionPath = "E:\\YuanyuanFJSP\\FJSP\\FJSP\\BRdata\\Mk01.txt";
		 //System.out.println("solutionPath:" + solutionPath);
		
		 int makeSpan = mapso.run(solutionPath);
		 long estimatedTime = System.currentTimeMillis() - initTime;
		 System.out.println(estimatedTime);
		 System.out.println(makeSpan);
	}
}
