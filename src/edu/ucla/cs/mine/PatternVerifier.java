package edu.ucla.cs.mine;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;

public class PatternVerifier {
	
	public ArrayList<String> pattern;
	
	public PatternVerifier() {
		pattern = new ArrayList<String>();
		pattern.add("new File");
		pattern.add("exists");
		pattern.add("IF {");
		pattern.add("createNewFile");
		pattern.add("}");
	}
	
	public ArrayList<ArrayList<String>> readAPISeqeunces(String path){
		ArrayList<ArrayList<String>> seqs = new ArrayList<ArrayList<String>>();
		
		try (BufferedReader br = new BufferedReader(new FileReader(new File(path)))){
			String line;
			while((line = br.readLine()) != null) {
				if(line.contains("---")){
					String s = line.split("---")[1];
					s = s.substring(1, s.length() - 1);
					ArrayList<String> seq = new ArrayList<String>();
					for(String api : s.split(",")){
						seq.add(api.trim());
					}
					seqs.add(seq);
				}
			}
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		return seqs;
	}
	
	public void verify(String path){
		ArrayList<ArrayList<String>> seqs = readAPISeqeunces(path);
		ArrayList<String> temp = new ArrayList<String>(pattern);
		int support = 0;
		for(ArrayList<String> seq : seqs){
			for(String api : seq){
				String s = temp.get(0);
				if(api.equals(s)) {
					temp.remove(0);
					if(temp.isEmpty()) {
						support ++;
						break;
					}
				}
			}
			
			// reset
			temp.clear();
			temp.addAll(pattern);
		}
		
		System.out.println(support);
	}
	
	public static void main(String[] args){
		String output = "/home/troy/research/BOA/Slicer/example/output.txt";
		PatternVerifier pv = new PatternVerifier();
		pv.verify(output);
	}

}
