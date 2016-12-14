package edu.ucla.cs.model;

import java.util.ArrayList;

public class MethodCall {
	public ArrayList<String> args;
	public String name;
	
	public MethodCall(String name, String args) {
		this.name = name;
		this.args = new ArrayList<String>();
		String[] arr = args.split(",");
		for(int i = 0; i < arr.length; i++) {
			this.args.add(arr[i]);
		}
	}
	
	@Override
	public boolean equals(Object o){
		if (!(o instanceof MethodCall)) {
			return false;
		}
		
		MethodCall that = (MethodCall)o;
		return this.name.equals(that.name) && this.args.equals(that.args);
	}
	
	@Override
	public int hashCode() {
		int hash = 1;
		hash = hash + 17 * this.name.hashCode();
		hash = hash + 31 * this.args.hashCode();
		return hash;
	}
	
	@Override
	public String toString(){
		return this.name + "->"+ this.args.toString();
	}
}
