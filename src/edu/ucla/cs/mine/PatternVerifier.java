package edu.ucla.cs.mine;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;

public class PatternVerifier {
	public HashMap<String, ArrayList<String>> seqs;
	public ArrayList<String> pattern;
	public HashMap<String, ArrayList<String>> support;
	
	public PatternVerifier(ArrayList<String> pattern) {
		this.pattern = pattern;
		this.seqs = new HashMap<String, ArrayList<String>>();
		this.support = new HashMap<String, ArrayList<String>>();
	}
	
	public void readAPISeqeunces(String path){
		try (BufferedReader br = new BufferedReader(new FileReader(new File(path)))){
			String line;
			while((line = br.readLine()) != null) {
				if(line.contains("---")){
					String id = line.split("---")[0];
					String s = line.split("---")[1];
					s = s.substring(1, s.length() - 1);
					ArrayList<String> seq = new ArrayList<String>();
					for(String api : s.split(",")){
						seq.add(api.trim());
					}
					seqs.put(id, seq);
				}
			}
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}	
	}
	
	public void verify(String path){
		readAPISeqeunces(path);
		
		if(pattern.isEmpty()) {
			for(String id : seqs.keySet()) {
				support.put(id, seqs.get(id));
			}
			
			return;
		}
		
		ArrayList<String> temp = new ArrayList<String>(pattern);
		for(String id : seqs.keySet()){
			ArrayList<String> seq = seqs.get(id); 
			for(String api : seq){
				String s = temp.get(0);
				if(api.equals(s)) {
					temp.remove(0);
					if(temp.isEmpty()) {
						support.put(id, seq);
						break;
					}
				}
			}
			
			// reset
			temp.clear();
			temp.addAll(pattern);
		}
	}
	
	public static void main(String[] args){
		String output = "/home/troy/research/BOA/Slicer/example/output_with_call_in_predicates.txt";
		ArrayList<String> pattern = new ArrayList<String>();
		pattern.add("new File");
		//pattern.add("exists");
		//pattern.add("IF {");
		pattern.add("createNewFile");
		//pattern.add("}");
		PatternVerifier pv = new PatternVerifier(pattern);
		pv.verify(output);
		System.out.print(pv.support.size());
	}
}
