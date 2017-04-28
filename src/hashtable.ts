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

export class Hashtable {
  table: any = null;
}

class HashNode {
  hashnumber: any;
  values: any[] = [];
  lt_child: any = null;
  gt_child: any = null;

  constructor(key: any) {
    this.hashnumber = key.hash_key_value;
  }
}

// True if the key object has a hash key value
function hasHashKeyValueForObject(key: any)
{
 return (key.hash_key_value != undefined);
}

// Gives the key object a hash key value, if needed
function setHashKeyValueForObject(key: any)
{
 if (key.hash_key_value == undefined)
  key.hash_key_value = Math.random();
}

// pair is a convenience object for holding two objects
export class Pair {
  constructor(public first: any, public second: any) {
  }
}

///////////////////////////////////
// hash* functions for Hashtables
///////////////////////////////////

// Get value from key object in hashtable, return undefined if key not found
export function hashGet(hashtable: any, key: any)
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
export function hashPut(hashtable: any, key: any, value: any)
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
function hashNodeFind(node: any, key: any)
{var v;

 v = node.values[hashNodeFindIndex(node,key)];
 if (v != undefined)
  return v.second;
 else
  return undefined;
}

// Set value for key object in node
function hashNodeSet(node: any, key: any, value: any)
{var i = hashNodeFindIndex(node,key);

 if (i < 0)
  i = node.values.length;

 node.values[i] = new Pair(key,value);

 return i;
}

// Get index for key object in hashtable, returns -1 if key not found
function hashNodeFindIndex(node: any, key: any)
{var v;

 for (var i = 0; i < node.values.length; i++)
 {
  if ((v = node.values[i]) != undefined && v.first == key)
   return i;
 }
 return -1;
}
