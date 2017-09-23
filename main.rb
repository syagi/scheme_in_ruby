
#組み込み関数の定義
$primitive_fun_env = {
  :+ => [:prim, lambda{|x,y| x+y}],
  :- => [:prim, lambda{|x,y| x-y}],
  :* => [:prim, lambda{|x,y| x*y}],
  :> => [:prim, lambda{|x,y| x>y}],
  :< => [:prim, lambda{|x,y| x<y}],
  :>= => [:prim, lambda{|x,y| x>=y}],
  :<= => [:prim, lambda{|x,y| x<=y}],
  :== => [:prim, lambda{|x,y| x==y}],
}

$boolean_env =
  {:true => true, :false => false}

$list_env = {
  :nil   => [],
  :null? => [:prim, lambda{|list| null?(list)}],
  :cons  => [:prim, lambda{|a, b| cons(a, b)}],
  :car   => [:prim, lambda{|list| car(list)}],
  :cdr   => [:prim, lambda{|list| cdr(list)}],
  :list  => [:prim, lambda{|list| list(*list)}],
}

$global_env =
  [$primitive_fun_env, $boolean_env, $lst_env]


#インタプリタ
def repl
  prompt = '>>> '
  second_prompt = '> '
  while true
    print prompt
    line = gets or return
    while line.count('(') > line.count(')')
      print second_prompt
      next_line = gets or return
      line += next_line
    end
    redo if line =~ /\A\s*\z/m
    begin
      val = _eval(parse(line), $global_env)
    rescue Exception => e
      puts e.to_s
      puts e.backtrace
      redo
    end
    puts pp(val)
  end
end

def closure?(exp)
  exp[0] == :closure
end

def pp(exp)
  if exp.is_a?(Symbol) or num?(exp)
    exp.to_s
  elsif exp == nil
    'nil'
  elsif exp.is_a?(Array) and closure?(exp)
    parameter, body, env = exp[1], exp[2], exp[3]
    "(closure #{pp(parameter)} #{pp(body)})"
  elsif exp.is_a?(Array) and lambda?(exp)
    parameter, body = exp[1], exp[2]
    "(lambda #{pp(parameters)} #{pp(body)})"
  elsif exp.is_a?(Hash)
    if exp == $primitive_fun_env
      '*primitive_fun_env*'
    elsif exp == $boolean_env
      '*boolean_env*'
    elsif exp == $list_env
      '*list_env*'
    else
      '{' + exp.map{|k,v| pp(k) + ':' + pp(v)}.join('.') + '}'
    end
  elsif exp.is_a?(Array)
    '(' + exp.map{|e| pp(e)}.join(',') + ')'
  else
    exp.to_s
  end
end

# 評価関数
def _eval(exp,env)
  if not list?(exp)
    if immediate_val?(exp)
      # 即値ならそのまま返す
      exp
    else
      lookup_var(exp,env)
    end
  else
    if special_form?(exp)
      eval_special_form(exp,env)
    else
      fun = _eval(car(exp),env)
      args = eval_list(cdr(exp),env)
      apply(fun, args)
    end
  end
end

#パーサー
def parse(exp)
  program = exp.strip().
    gsub(/[a-zA-Z\+\-\*><=][0-9a-zA-Z\+\-=!*]*/, ':\\0').
    gsub(/\s+/, ', ').
    gsub(/\(/, '[').
    gsub(/\)/, ']')
  eval(program)
end

#lambdaの評価
# args
#   exp lambda式
#   env 環境
def eval_lambda(exp,env)
  make_closure(exp,env)
end

def make_closure(exp,env)
  parameters, body = exp[1], exp[2]
  [:closure, parameters, body, env]
end

def lambda_apply(closure,args)
  parameters, body, env = closure_to_parameters_body_env(closure)
  new_env = extend_env(parameters, args, env)
  _eval(body, new_env)
end

def closure_to_parameters_body_env(closure)
  [closure[1], closure[2], closure[3]]
end

#letの評価
#lambda式に書き換えた上で_evalに渡す
# args
#   exp let式
#    e.g. [:let, [[:parameter,arg]...], body]
#   env 環境
def eval_let(exp, env)
  parameters, args, body = let_to_parameters_args_body(exp)
  new_exp = [[:lambda, parameters, body]] + args
  _eval(new_exp, env)
end

#let式から仮引数、引数、式を抜き出す
# args
#  exp let式
# return
#  1 parameters 仮引数
#  2 args 引数
#  3 body 式
def let_to_parameters_args_body(exp)
  [exp[1].map{|e| e[0]}, exp[1].map{|e| e[1]}, exp[2]]
end

#letrec
def eval_letrec(exp, env)
  parameters, args, body = letrec_to_parameters_args_body(exp)
  tmp_env = Hash.new
  parameters.each do |parameter|
    tmp_env[parameter] = :dummy
  end
  ext_env = extend_env(tmp_env.keys(), tmp_env.values(), env)
  args_val = eval_list(args, ext_env)
  set_extend_env!(parameters, args_val, ext_env)
  new_exp = [[:lambda, parameters, body]] + args
  _eval(new_exp, ext_env)
end

def set_extend_env!(parameters, args_val, ext_env)
  parameters.zip(args_val).each do |parameter, args_val|
    ext_env[0][parameter] = args_val
  end
end

def letrec_to_parameters_args_body(exp)
  let_to_parameters_args_body(exp)
end


#ifの評価
#
def eval_if(exp,env)
  cond, true_clause, false_clause = if_to_cond_true_false(exp)
  if _eval(cond, env)
    _eval(true_clause, env)
  else
    _eval(false_clause, env)
  end
end

#if文から状態、真、偽それぞれのクロージャを取り出す
def if_to_cond_true_false(exp)
  [exp[1], exp[2], exp[3]]
end

def eval_cond(exp, env)
  if_exp = cond_to_if(cdr(exp))
  eval_if(if_exp, env)
end

def cond_to_if(cond_exp)
  if cond_exp == []
    ''
  else
    e = car(cond_exp)
    p, c = e[0], e[1]
    if p == :else
       p == :true
    end
    [:if, p, c, cond_to_if(cdr(cond_exp))]
  end
end


def eval_quote(exp, env)
  car(cdr(exp))
end


def eval_special_form(exp, env)
  if lambda?(exp)
    eval_lambda(exp, env)
  elsif let?(exp)
    eval_let(exp,env)
  elsif letrec?(exp)
    eval_letrec(exp,env)
  elsif if?(exp)
    eval_if(exp,env)
  end
end

####判断系メソッド#####
#listインスタンスかの判断
def list?(exp)
  exp.is_a?(Array)
end

def null?(list)
  list == []
end

#即値の判断
def immediate_val?(exp)
  num?(exp)
end

def num?(exp)
  exp.is_a?(Numeric)
end

#式の判断
def let?(exp)
  exp[0] == :let
end

def letrec?(exp)
  exp[0] == :letrec
end

def lambda?(exp)
  exp[0] == :lambda
end

def if?(exp)
  exp[0] == :if
end

def cond?(exp)
  exp[0] == :cond
end

def define?(exp)
  exp[0] == :define
end

def quote?(exp)
  exp[0] == :quote
end

def special_form?(exp)
  lambda?(exp) or
     let?(exp) or
     letrec?(exp) or
     if?(exp) or
     cond?(exp) or
     define?(exp) or
     quote?(exp)
end

def primitive_fun?(exp)
  exp[0] == :prim
end

#組み込み関数かの判断
def lookup_primitive_fun(exp)
  $primitive_fun_env[exp]
end
#関数適用
def apply(fun, args)
  if primitive_fun?(fun)
    apply_primitive_fun(fun, args)
  else
    lambda_apply(fun, args)
  end
end

def apply_primitive_fun(fun, args)
  fun_val = fun[1]
  fun_val.call(*args)
end

#list関連
#  参考
#   https://en.wikipedia.org/wiki/CAR_and_CDR
def eval_list(exp, env)
  exp.map{|e| _eval(e, env)}
end

def list (*list)
  list
end

def cons(a,b)
  if not list?(b)
    raise "sorry, we haven't implemented yet..."
  else
    [a] + b
  end
end

# car ("Contents of the Address part of Register number")
def car(list)
  list[0]
end
# cdr ("Contents of the Decrement part of Register number")
def cdr(list)
  list[1..-1]
end

#定義
#
def eval_define(exp, env)
  if define_with_parameter?(exp)
    var, val = define_with_parameter_var_val(exp)
  else
    var, val = define_var_val(exp)
  end
  var_ref = lookup_var_ref(var, env)
  if var_ref != nil
    var_ref[var] = _eval(val, env)
  else
    extend_env!([var], [_eval(val, env)], env)
  end
  nil
end

def extend_env!(parameters, args, env)
  alist = prameters.zip(args)
  h = Hash.new
  alist.each { |k, v| h[k] = v }
  env.unshift(h)
end

def define_with_parameter?(exp)
  list?(exp[1])
end

def define_with_parameter_var_val(exp)
  var = car(exp[1])
  parameters, body = cdr(exp[1]), exp[2]
  val = [:lambda, parameters, body]
  [var, val]
end

def define_var_val(exp)
  [exp[1], exp[2]]
end

def lookup_var_ref(var, env)
  env.find{|alist| alist.key?(var)}
end


#変数を見つける
def lookup_var(var, env)
  alist = env.find{|alist| alist.key?(var)}
  if alist == nil
    raise "couldn't find value to variables: '#{var}'"
  end
  alist[var]
end

#環境の拡張
def extend_env(parameters, args, env)
  alist = parameters.zip(args)
  h = Hash.new
  alist.each { |k, v| h[k] = v }
  [h] + env
end

def run(exp)
  puts exp.to_s
  puts _eval(exp, $global_env)
end

repl
