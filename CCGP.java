package TFSCompared;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
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

public class CCGP {
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

	boolean updated;

	Random ran = new Random();

	double[][] G0;
	double[][] G1;
	double[][] G2;
	double[] gBest;
	
	int[] solVal;

	int bestSolIndex;
	int bestSolVal;
	
	int hisBetSolVal;
	
	int[] NG = {240,480};
	int NGI;
	int[][] groupIndices;
	ArrayList<double[][]> g0;
	ArrayList<double[][]> g1;
	ArrayList<double[][]> g2; //保存分组最优，用于分组内邻域搜索解的推进
	ArrayList<double[]> gpBests;
	ArrayList<int[]> gpSolVals;
	ArrayList<Integer> bestSolVals;
	
	
	void initializeParameters() {
		NP = 30; // popSize
		NI = 20; // iteration

		ND = ShopData.getTotalOpNum() * 2; // dimension
		NGI = 10;
		updated = false;

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
		
		hisBetSolVal = bestSolVal;
		gBest = G0[bestSolIndex].clone();
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
		initializeGroupPopulation();
	}

	void initializeGroupPopulation() {
		g0 = new ArrayList<double[][]>();
		g1 = new ArrayList<double[][]>();
		g2 = new ArrayList<double[][]>();
		gpSolVals = new ArrayList<int []>();
		gpBests = new ArrayList<double[]>();
		bestSolVals = new ArrayList<Integer>();
		// TODO Auto-generated method stub
		for(int gpIndex = 0; gpIndex < groupIndices.length; gpIndex++){
			g0.add(G2.clone());
			g1.add(G2.clone());
			g2.add(G2.clone());
		}
		
		for(int gpIndex = 0; gpIndex < groupIndices.length; gpIndex++){
			int [] bestVal = solVal.clone();
			gpSolVals.add(bestVal);
			gpBests.add(gBest);
			bestSolVals.add(bestSolVal);
		}
	}

	public int run() {
		// count = 0;
		// Timer timer = new Timer();
		// timer.schedule(new MyTask(), 40, 5000);

		int iter, i, j;
		initializeParameters();
		initializePopulation();
		initializeGrouping();

		for (iter = 1; iter <= NI; iter++) {
			if (iter > 1 && !updated) {
				initializeGrouping();
			}
			for (int gpIndex = 0; gpIndex < groupIndices.length; gpIndex++) {
				for (int gpIter = 0; gpIter < NGI; gpIter++) {
					for (i = 0; i < NP; i++){
						int R1, R2;
						do {
							R1 = ran.nextInt(NP);
						} while (R1 == i);
						do {
							R2 = ran.nextInt(NP);
						} while (R2 == i || R2 == R1);

						for (j = 0; j < groupIndices[gpIndex].length; j++) {
							int dim = groupIndices[gpIndex][j];
							if (ran.nextDouble() < Cr) {
								G1[i][dim] = G0[bestSolIndex][dim] + F * (G0[R1][dim] - G0[R2][dim]);
								if(G1[i][dim] > delta)
									G1[i][dim] = delta;
								if(G1[i][dim] < -delta)
									G1[i][dim] = -delta;
							} else
								G1[i][dim] = G0[i][dim];
						}
					}
					
					for (i = 0; i < NP; i++) {
						double[] newG1 = gBest.clone();
						for (j = 0; j < groupIndices[gpIndex].length; j++) {
							int dim = groupIndices[gpIndex][j];
							newG1[dim] = G1[i][dim];
						}
						int[] perm = addjustOrder(newG1, ND);
						if (ran.nextDouble() < 0.5) {
							FJSPSolution curSolution = new FJSPSolution(perm, ND);
							FJSPSolution newSolution = new TestLocalSearch(curSolution, localIterTimes).run();
							reArrange(newG1, newSolution.getPermutation(), ND);
						}
						int val = getFunctionVal(newG1, ND);
						if (val < gpSolVals.get(gpIndex)[i]) {
							gpSolVals.get(gpIndex)[i] = val; 
							for (j = 0; j < groupIndices[gpIndex].length; j++) {
								int dim = groupIndices[gpIndex][j];
								G2[i][dim] = newG1[dim];
							}
						} else
							for (j = 0; j < groupIndices[gpIndex].length; j++) {
								int dim = groupIndices[gpIndex][j];
								G2[i][dim] = G0[i][dim];
						}
					}
					
					bestSolVal = Integer.MAX_VALUE;
					bestSolIndex = -1;

					for (i = 0; i < NP; i++) {
						if (gpSolVals.get(gpIndex)[i] < bestSolVal) {
							bestSolVal = gpSolVals.get(gpIndex)[i];
							bestSolIndex = i;
						}
					}
					
					//gpBests.set(gpIndex, g2.get(gpIndex)[bestSolIndex].clone());
					gpBests.set(gpIndex, G2[bestSolIndex].clone());
					bestSolVals.set(gpIndex, bestSolVal);
					
					if(bestSolVal < hisBetSolVal){
						for (j = 0; j < groupIndices[gpIndex].length; j++) {
							int dim = groupIndices[gpIndex][j];
							//gBest[dim] = g2.get(gpIndex)[bestSolIndex][dim];
							gBest[dim] = G2[bestSolIndex][dim];
						}
					}
					
//					double[][] GX = g0.get(gpIndex).clone();
//					g0.set(gpIndex, g2.get(gpIndex));
//					g2.set(gpIndex, GX);
					double[][] GX = G0.clone();
					G0 = G2.clone();
					G2 = GX.clone();
				}
			}
			
			int preHisVal = hisBetSolVal;
			for(int gpIndex = 0; gpIndex < groupIndices.length; gpIndex++){
				if(bestSolVals.get(gpIndex) < hisBetSolVal){
					hisBetSolVal = bestSolVals.get(gpIndex);
					gBest = gpBests.get(gpIndex).clone();
				}
			}
			System.out.println("CCGP iteration:" + iter + ":" + "gBest: " + hisBetSolVal);
			if(hisBetSolVal < preHisVal){
				updated = true;
			}
		}
		/*
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
	public static void main(String[] args) throws FileNotFoundException {

		// System.out.println("0.9 100 n1");
		/*
		 * System.out.println("mk02"); // System.out.println("500 10000 0.5 0.3"
		 * ); new ShopData("E:\\Data\\BRdata\\mk02.fjs"); CDE cde = new CDE();
		 * 
		 * int runTimes = 50; int[] mArray = new int[runTimes]; long[] cpuTime =
		 * new long[runTimes]; for (int i = 1; i <= runTimes; i++) { long
		 * startTime = System.currentTimeMillis(); int makeSpan = cde.run();
		 * long endTime = System.currentTimeMillis(); mArray[i - 1] = makeSpan;
		 * cpuTime[i - 1] = endTime - startTime; System.out.println(makeSpan);
		 * System.out.println("��������ʱ�䣺 " + cpuTime[i - 1] + "ms"); }
		 * analysisResult(mArray, cpuTime, runTimes);
		 */

		/*
		 * File file = new File("G:\\NB_Data\\DS_3"); File[] array =
		 * file.listFiles();
		 * 
		 * String targetFilePath = "G:\\NBResult_OTHER_6";
		 * 
		 * int runTimes = 100;
		 * 
		 * for (int i = 0; i < array.length; i++) {
		 * 
		 * String filePath = array[i].getAbsolutePath();
		 * 
		 * int index1 = array[i].getAbsolutePath().lastIndexOf("\\"); int index2
		 * = array[i].getAbsolutePath().indexOf(".");
		 * 
		 * String fileName = filePath.substring( index1 + 1, index2);
		 * 
		 * 
		 * new ShopData(filePath); CDE cde = new CDE();
		 * 
		 * System.out.println(filePath); for (int j = 0; j < runTimes; j++){
		 * System.out.println(j + 1); String outName = targetFilePath +
		 * "\\" + fileName +  "_" + (j + 1) + ".txt";
		 * 
		 * long startTime = System.currentTimeMillis(); int makeSpan =
		 * cde.run(); long endTime = System.currentTimeMillis();
		 * 
		 * System.out.println(makeSpan); System.out.println("��������ʱ�䣺 " +
		 * (endTime - startTime) + "ms");
		 * 
		 * 
		 * 
		 * FJSPSolution sol = new
		 * FJSPSolution(cde.getBestPerm(),ShopData.getTotalOpNum() * 2);
		 * sol.saveSolution(outName);
		 * 
		 * } }
		 */

		/*
		 * File file = new File("F:\\DPdata_6");
		 * 
		 * String outPath = "F:\\DEResultForDP\\"; String targetPath =
		 * "F:\\DPBestSolution\\"; File[] array = file.listFiles();
		 * 
		 * int runTimes = 50;
		 * 
		 * int[] mArray = new int[runTimes]; long[] cpuTime = new
		 * long[runTimes]; CDE cde = new CDE(); for (int i = 0; i <
		 * array.length; i++) { new ShopData(array[i].getAbsolutePath()); int
		 * index1 = array[i].getAbsolutePath().lastIndexOf("\\"); int index2 =
		 * array[i].getAbsolutePath().indexOf("."); String path =
		 * array[i].getAbsolutePath().substring(index1 + 1, index2); String
		 * newPath = outPath + path + ".txt"; OutputStreamWriter osw = new
		 * OutputStreamWriter( new FileOutputStream(newPath)); PrintWriter pw =
		 * new PrintWriter(osw); for (int j = 0; j < runTimes; j++) {
		 * 
		 * long initTime = System.currentTimeMillis(); int makeSpan = cde.run();
		 * long estimatedTime = System.currentTimeMillis() - initTime;
		 * 
		 * System.out.println(makeSpan); pw.println(makeSpan);
		 * 
		 * System.out.println("����ʱ�䣺 " + estimatedTime); pw.println("����ʱ�䣺 "
		 * + estimatedTime);
		 * 
		 * mArray[j] = makeSpan; cpuTime[j] = estimatedTime;
		 * 
		 * 
		 * String outName = targetPath + "\\" + path+  "_" + (j + 1) + ".txt";
		 * FJSPSolution sol = new
		 * FJSPSolution(cde.getBestPerm(),ShopData.getTotalOpNum() * 2);
		 * sol.saveSolution(outName);
		 * 
		 * } double[] result = analysisResult_N(mArray, cpuTime, runTimes);
		 * 
		 * System.out.println("Best: " + result[0]); System.out.println("Ave: "
		 * + result[1]); System.out.println("SD: " + result[2]);
		 * System.out.println("AVCPU: " + result[3]);
		 * 
		 * pw.println("Best: " + result[0]); pw.println("Ave: " + result[1]);
		 * pw.println("SD: " + result[2]); pw.println("AVCPU: " + result[3]);
		 * pw.close(); }
		 */

		for (int i = 1; i <= 10; i++) {
			new ShopData("E:\\YuanyuanFJSP\\FJSP\\FJSP\\BRdata\\Mk10.fjs");
			CCGP ccgp = new CCGP();
			long initTime = System.currentTimeMillis();
			int makeSpan = ccgp.run();
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
