local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv)
	local 1 = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 79) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local l = gBits32();
		local r = gBits32();
		return (("-2" * gBit(r, 32)) + 1) * (2 ^ (gBit(r, 21, 31) - 1023)) * ((((gBit(r, 1, 20) * (2 ^ 32)) + l) / (2 ^ 52)) + 1);
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local {} = {};
		for Idx = 1, #Str do
			({})[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat({});
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local {} = {};
		local {} = {};
		local {} = {};
		local {{},{},nil,{}} = {{},{},nil,{}};
		local ConstCount = gBits32();
		local {} = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			({})[Idx] = Cons;
		end
		({{},{},nil,{}})[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local {gBits16(),gBits16(),nil,nil} = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					({gBits16(),gBits16(),nil,nil})[3] = gBits16();
					({gBits16(),gBits16(),nil,nil})[4] = gBits16();
				elseif (Type == 1) then
					({gBits16(),gBits16(),nil,nil})[3] = gBits32();
				elseif (Type == 2) then
					({gBits16(),gBits16(),nil,nil})[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					({gBits16(),gBits16(),nil,nil})[3] = gBits32() - (2 ^ 16);
					({gBits16(),gBits16(),nil,nil})[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					({gBits16(),gBits16(),nil,nil})[2] = ({})[({gBits16(),gBits16(),nil,nil})[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					({gBits16(),gBits16(),nil,nil})[3] = ({})[({gBits16(),gBits16(),nil,nil})[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					({gBits16(),gBits16(),nil,nil})[4] = ({})[({gBits16(),gBits16(),nil,nil})[4]];
				end
				({})[Idx] = {gBits16(),gBits16(),nil,nil};
			end
		end
		for Idx = 1, gBits32() do
			({})[Idx - 1] = Deserialize();
		end
		for Idx = 1, gBits32() do
			({})[Idx] = gBits32();
		end
		return {{},{},nil,{}};
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local 1 = 1;
			local "-1" = "-1";
			local {...} = {...};
			local PCount = Select("#", ...) - 1;
			local function Loop()
				local Instr = Instr;
				local Const = Const;
				local Proto = Proto;
				local Params = Params;
				local _R = _R;
				local {} = {};
				local {} = {};
				local {} = {};
				for Idx = 0, PCount do
					if (Idx >= Params) then
						({})[Idx - Params] = ({...})[Idx + 1];
					else
						({})[Idx] = ({...})[Idx + 1];
					end
				end
				local Varargsz = (PCount - Params) + 1;
				local Inst;
				local Enum;
				while true do
					Inst = Instr[VIP];
					Enum = Inst[1];
					if (Enum <= 2) then
						if (Enum <= 0) then
							({})[Inst[2]] = Env[Inst[3]];
						elseif (Enum > 1) then
							({})[Inst[2]] = Inst[3];
						else
							({})[Inst[2]] = ({})[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 3) then
						local A = Inst[2];
						local B = ({})[Inst[3]];
						({})[A + 1] = B;
						({})[A] = B[Inst[4]];
					elseif (Enum > 4) then
						do
							return;
						end
					else
						local A = Inst[2];
						({})[A](Unpack({}, A + 1, Inst[3]));
					end
					VIP = VIP + 1;
				end
			end
			A, B = _R(PCall(Loop));
			if not A[1] then
				local line = Chunk[4][1] or "?";
				error("Script error at [" .. line .. "]:" .. A[2]);
			else
				return Unpack(A, 2, B);
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)();
end
VMCall("LOL!053O0003043O0067616D6503073O00506C6179657273030B3O004C6F63616C506C6179657203043O004B69636B03343O00506C6561736520636865636B20796F757220696E7465726E657420636F2O6E656374696F6E20616E642074727920616761696E2E00073O00124O00013O0020015O00020020015O00030020035O0004001202000200054O00043O000200012O00053O00017O00073O00013O00013O00013O00013O00013O00013O00013O00", GetFEnv());
