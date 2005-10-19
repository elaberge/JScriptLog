/*******
    This file is part of JScriptLog.  This notice must remain.

    Created by Glendon Holst.  Copyright 2005.
    
    JLog is free software licensed under the GNU General Public License.
	See the included LICENSE.txt and GNU.txt files.

    Check <http://jlogic.sourceforge.net/> for further information.
*******/

///////////////////////////////////
// * Hash*
// A Hashtable that supports unnamed objects as keys.
//
//// Properties added to key objects (document here):
// key.hash_key_value : the value used to order and find keys
//
///////////////////////////////////

function Hashtable()
{
 this.table = null;

 return this;
}

function HashNode(key)
{
 this.hashnumber = key.hash_key_value;
 this.values = new Array();
 this.lt_child = null;
 this.gt_child = null;
 
 return this;
}

// True if the key object has a hash key value
function hasHashKeyValueForObject(key)
{
 return (key.hash_key_value != undefined);
}

// Gives the key object a hash key value, if needed
function setHashKeyValueForObject(key)
{
 if (key.hash_key_value == undefined)
  key.hash_key_value = Math.random();
}

// pair is a convenience object for holding two objects
function Pair(first, second)
{
 this.first = first;
 this.second = second;
 return this;
}

///////////////////////////////////
// hash* functions for Hashtables
///////////////////////////////////

// Get value from key object in hashtable, return undefined if key not found
function hashGet(hashtable,key)
{var node = hashtable.table;

 if (key.hash_key_value == undefined)
  return undefined;
 
 while (node != null)
 {
  if (key.hash_key_value < node.hashnumber)
   node = node.lt_child;
  else if (key.hash_key_value > node.hashnumber)
   node = node.gt_child;
  else
   return hashNodeFind(node,key); 
 }

 return undefined;
}

// Add key:value pair to hashtable
function hashPut(hashtable,key,value)
{var prev = null;
 var node = hashtable.table;

 setHashKeyValueForObject(key);

 while (node != null)
 {
  prev = node;
  
  if (key.hash_key_value < node.hashnumber)
   node = node.lt_child;
  else if (key.hash_key_value > node.hashnumber)
   node = node.gt_child;
  else
   return hashNodeSet(node,key,value); 
 }

 node = new HashNode(key);
 
 if (prev == null)
  hashtable.table = node;
 else if (node.hashnumber < prev.hashnumber)
  prev.lt_child = node;
 else if (node.hashnumber > prev.hashnumber)
  prev.gt_child = node;
 else
  throw new Error("Hashtable corrupted."); 
  
 return hashNodeSet(node,key,value);
}

// Get value from key object in node, return undefined if key not found
function hashNodeFind(node,key)
{var v;

 v = node.values[hashNodeFindIndex(node,key)];
 if (v != undefined)
  return v.second;
 else
  return undefined;
}

// Set value for key object in node
function hashNodeSet(node,key,value)
{var i = hashNodeFindIndex(node,key);

 if (i < 0)
  i = node.values.length;

 node.values[i] = new Pair(key,value);
  
 return i;
}

// Get index for key object in hashtable, returns -1 if key not found
function hashNodeFindIndex(node,key)
{var i;
 var v;
 
 for (i = 0; i < node.values.length; i++)
 {
  if ((v = node.values[i]) != undefined && v.first == key)
   return i;
 }
 return -1;
}

